/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Thomas Murrills
-/

/-
# Dependency graphs at scale

Reachability and label propagation over large dependency graphs (all constants of Mathlib, say),
without recursion and without per-step tree-map operations.

Ported from ImportGraph (`ImportGraph/Imports/RequiredModules.lean`,
leanprover-community/import-graph at `16f02aa`): the worklist of
`NameSet.transitivelyUsedConstants` (here `Graph.explore`) and the explicit-stack, memoised
traversal of `Environment.transitivelyRequiredModules'` (here `Graph.flowBackward`). Changes:
* generic in the vertex type and in the label type (any `Union`, e.g. `Agitate.ImportGraph.Bitset`)
  instead of `Name` and `BitVec N`;
* vertices are numbered densely, so the traversals use arrays instead of `NameMap`/`NameSet`, and
  discovery uses a `Std.HashMap` instead of `NameSet.min!`/`erase` per step;
* cycles are allowed: labels propagate over strongly connected components (an iterative Tarjan),
  since graphs derived from constants, such as source declarations, can be cyclic (mutual
  inductives). Core's `Lean.SCC.scc` recurses, which overflows the stack at this scale (as
  ImportGraph notes for its own traversal);
* labels can also flow forwards, from users to what they use (`Graph.flowForward`).

`Agitate.ImportGraph.Environment` re-expresses ImportGraph's functions with these.
-/
module

public import Std.Data.HashMap.Basic

public section

namespace Agitate.ImportGraph

/-- A directed graph on the vertices `0, …, size - 1`, given by successor lists. -/
structure Graph where
  succs : Array (Array Nat)
deriving Inhabited

namespace Graph

def size (g : Graph) : Nat := g.succs.size

/-- The part of a graph reachable from some roots, with its vertices numbered densely. -/
structure Explored (α : Type) [BEq α] [Hashable α] where
  verts : Array α
  /-- The inverse of `verts`. -/
  index : Std.HashMap α Nat
  graph : Graph

/--
The vertices reachable from `roots` along `succ`, numbered densely in breadth-first discovery
order (the distinct roots first), with the graph between them. `succ` is called once per vertex;
repeated successors are kept as repeated edges, which none of the traversals below mind.
-/
def explore {α : Type} [BEq α] [Hashable α] (roots : Array α) (succ : α → Array α) :
    Explored α := Id.run do
  let mut index : Std.HashMap α Nat := {}
  let mut verts : Array α := #[]
  for r in roots do
    if !index.contains r then
      index := index.insert r verts.size
      verts := verts.push r
  let mut succs : Array (Array Nat) := #[]
  -- `verts` is also the queue: `succs.size` is the next vertex to expand
  while succs.size < verts.size do
    let mut out := #[]
    let some v := verts[succs.size]? | break
    for w in succ v do
      match index[w]? with
      | some j => out := out.push j
      | none =>
        index := index.insert w verts.size
        out := out.push verts.size
        verts := verts.push w
    succs := succs.push out
  return { verts, index, graph := ⟨succs⟩ }

/--
The strongly connected components of the part of a graph reachable from some roots, in reverse
topological order: each component comes after every component reachable from it.
-/
structure Components where
  comps : Array (Array Nat)
  /-- `compOf[v]` is `v`'s component index plus one, or `0` if `v` was not reached. -/
  compOf : Array Nat

/-- Tarjan's algorithm from `roots`, with an explicit call stack. -/
def components (g : Graph) (roots : Array Nat) : Components := Id.run do
  let n := g.size
  -- `index[v]`: DFS number plus one (`0`: unvisited)
  let mut index : Array Nat := .replicate n 0
  let mut low : Array Nat := .replicate n 0
  let mut onStack : Array Bool := .replicate n false
  let mut stack : Array Nat := #[]
  -- the simulated recursion: a vertex and the position of its next successor
  let mut calls : Array (Nat × Nat) := #[]
  let mut next := 1
  let mut comps : Array (Array Nat) := #[]
  let mut compOf : Array Nat := .replicate n 0
  for r in roots do
    if index[r]! != 0 then continue
    index := index.set! r next; low := low.set! r next; next := next + 1
    stack := stack.push r; onStack := onStack.set! r true
    calls := calls.push (r, 0)
    while !calls.isEmpty do
      let (v, i) := calls.back!
      let vs := g.succs[v]!
      if h : i < vs.size then
        calls := calls.set! (calls.size - 1) (v, i + 1)
        let w := vs[i]
        if index[w]! == 0 then
          index := index.set! w next; low := low.set! w next; next := next + 1
          stack := stack.push w; onStack := onStack.set! w true
          calls := calls.push (w, 0)
        else if onStack[w]! then
          low := low.set! v (min low[v]! index[w]!)
      else
        calls := calls.pop
        if low[v]! == index[v]! then
          let c := comps.size + 1
          let mut comp := #[]
          repeat
            let w := stack.back!
            stack := stack.pop
            onStack := onStack.set! w false
            compOf := compOf.set! w c
            comp := comp.push w
            if w == v then break
          comps := comps.push comp
        if let some (u, _) := calls.back? then
          low := low.set! u (min low[u]! low[v]!)
  return { comps, compOf }

variable {σ : Type} [Union σ] [EmptyCollection σ] [Inhabited σ]

/--
Labels flowing along edges: for each vertex `v` reachable from `roots`, the union of `init u` over
the vertices `u` reachable from `roots` that reach `v` (`v` included). Unreached vertices get `∅`.
For "which roots use `v`", take `init` to be a root's own singleton and `∅` elsewhere.
-/
def flowForward (g : Graph) (roots : Array Nat) (init : Nat → σ) : Array σ := Id.run do
  let cs := g.components roots
  let mut label : Array σ := .replicate g.size ∅
  -- sources first: the reverse of `comps`
  for k' in 0...cs.comps.size do
    let k := cs.comps.size - 1 - k'
    let comp := cs.comps[k]!
    let mut acc : σ := ∅
    for v in comp do
      acc := acc ∪ init v ∪ label[v]!
    for v in comp do
      label := label.set! v acc
    for v in comp do
      for w in g.succs[v]! do
        if cs.compOf[w]! != k + 1 then
          label := label.modify w (· ∪ acc)
  return label

/--
Labels collected against the edges: for each vertex `v` reachable from `roots`, the union of
`init w` over the vertices `w` that `v` reaches (`v` included). Unreached vertices get `∅`. This is
ImportGraph's `transitivelyRequiredModules'` memo `c2m`, with `init v` the modules `v` uses.
-/
def flowBackward (g : Graph) (roots : Array Nat) (init : Nat → σ) : Array σ := Id.run do
  let cs := g.components roots
  let mut label : Array σ := .replicate g.size ∅
  -- sinks first: the order of `comps`
  for k in 0...cs.comps.size do
    let comp := cs.comps[k]!
    let mut acc : σ := ∅
    for v in comp do
      acc := acc ∪ init v
      for w in g.succs[v]! do
        if cs.compOf[w]! != k + 1 then
          acc := acc ∪ label[w]!
    for v in comp do
      label := label.set! v acc
  return label

end Graph

end Agitate.ImportGraph
