/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
# Dependency graphs at scale (upstreamable)

Graphs over dense vertices `0, …, n - 1` (all source declarations of Mathlib, say), stored in
compressed sparse row form: every edge in one array, plus an offset per vertex. Building one is a
counting sort of an edge list, so there is no allocation per vertex. Edges may carry a label byte
(`LGraph`), e.g. the kinds of a need (`Agitate.ImportGraph.NeedKinds`).

Graphs may be cyclic (mutual inductives make declaration graphs so): labels propagate over strongly
connected components, found by an iterative Tarjan. Core's `Lean.SCC.scc` recurses, which overflows
the stack at this scale. Nothing here recurses.
-/
module

public section

namespace Agitate.ImportGraph

/--
A directed graph on the vertices `0, …, size - 1`: the successors of `v` are
`targets[offsets[v]], …, targets[offsets[v + 1] - 1]`.
-/
structure Graph where
  /-- `size + 1` entries, ascending, from `0` to `targets.size`. -/
  offsets : Array Nat
  targets : Array Nat
deriving Inhabited

/-- A graph with a label byte per edge, aligned with `graph.targets`. -/
structure LGraph where
  graph : Graph
  labels : ByteArray
deriving Inhabited

namespace Graph

def size (g : Graph) : Nat := g.offsets.size - 1

/-- The number of edges. -/
def numEdges (g : Graph) : Nat := g.targets.size

/-- The successors of `v` are `targets` at `start v ≤ k < stop v`. -/
@[inline] def start (g : Graph) (v : Nat) : Nat := g.offsets[v]!
@[inline] def stop (g : Graph) (v : Nat) : Nat := g.offsets[v + 1]!

/-- The successors of `v`, as a new array (for tests and cold paths). -/
def succs (g : Graph) (v : Nat) : Array Nat := g.targets.extract (g.start v) (g.stop v)

/--
The graph on `n` vertices with the edges `srcs[k] → dsts[k]`, and the labels `labels[k]` permuted
alongside, by a counting sort (each vertex keeps its edges in input order). Every source must be
`< n`.
-/
def ofEdgesL (n : Nat) (srcs dsts : Array Nat) (labels : ByteArray) : LGraph := Id.run do
  let mut offsets : Array Nat := .replicate (n + 1) 0
  for s in srcs do
    offsets := offsets.modify (s + 1) (· + 1)
  for i in 0...n do
    offsets := offsets.set! (i + 1) (offsets[i + 1]! + offsets[i]!)
  -- `pos[v]`: where `v`'s next edge goes; starts as a copy of `offsets`
  let mut pos := offsets.extract 0 n
  let mut targets : Array Nat := .replicate srcs.size 0
  let mut out : ByteArray := ⟨.replicate srcs.size 0⟩
  for h : k in 0...srcs.size do
    let s := srcs[k]
    let p := pos[s]!
    targets := targets.set! p dsts[k]!
    out := out.set! p (labels.get! k)
    pos := pos.set! s (p + 1)
  return { graph := { offsets, targets }, labels := out }

/-- The graph whose successors of `v` are `succs[v]`. -/
def ofSuccs (succs : Array (Array Nat)) : Graph := Id.run do
  let mut offsets : Array Nat := #[0]
  let mut targets : Array Nat := #[]
  for ws in succs do
    targets := targets ++ ws
    offsets := offsets.push targets.size
  return { offsets, targets }

/-- `ofEdgesL` without labels. -/
def ofEdges (n : Nat) (srcs dsts : Array Nat) : Graph :=
  (ofEdgesL n srcs dsts ⟨.replicate srcs.size 0⟩).graph

/--
Strongly connected components of the part of a graph reachable from some roots, in reverse
topological order: each component comes after every component reachable from it.
-/
structure Components where
  comps : Array (Array Nat)
  /-- `compOf[v]` is `v`'s component index plus one, or `0` if `v` was not reached. -/
  compOf : Array Nat
deriving Inhabited

/-- Tarjan's algorithm from `roots`, with an explicit call stack. -/
def components (g : Graph) (roots : Array Nat) : Components := Id.run do
  let n := g.size
  -- `index[v]`: DFS number plus one (`0`: unvisited)
  let mut index : Array Nat := .replicate n 0
  let mut low : Array Nat := .replicate n 0
  let mut onStack : Array Bool := .replicate n false
  let mut stack : Array Nat := #[]
  -- the simulated recursion: a vertex and the position of its next edge in `targets`
  let mut calls : Array (Nat × Nat) := #[]
  let mut next := 1
  let mut comps : Array (Array Nat) := #[]
  let mut compOf : Array Nat := .replicate n 0
  for r in roots do
    if index[r]! != 0 then continue
    index := index.set! r next; low := low.set! r next; next := next + 1
    stack := stack.push r; onStack := onStack.set! r true
    calls := calls.push (r, g.start r)
    while !calls.isEmpty do
      let (v, k) := calls.back!
      if k < g.stop v then
        calls := calls.set! (calls.size - 1) (v, k + 1)
        let w := g.targets[k]!
        if index[w]! == 0 then
          index := index.set! w next; low := low.set! w next; next := next + 1
          stack := stack.push w; onStack := onStack.set! w true
          calls := calls.push (w, g.start w)
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
      for e in (g.start v)...(g.stop v) do
        let w := g.targets[e]!
        if cs.compOf[w]! != k + 1 then
          label := label.modify w (· ∪ acc)
  return label

/--
A breadth-first search tree from `roots`: `pred[v]` is one plus the index (into `targets`) of the
edge by which `v` was first reached, `0` for roots and unreached vertices, and `reached[v]` says
whether `v` was reached. Following `pred` from `v` gives a shortest path from a root.
-/
structure BfsTree where
  pred : Array Nat
  /-- The source vertex of each edge (`edgeSrc[k]` for `targets[k]`). -/
  edgeSrc : Array Nat
  reached : Array Bool
deriving Inhabited

/-- Breadth-first search from `roots`. -/
def bfs (g : Graph) (roots : Array Nat) : BfsTree := Id.run do
  let mut pred : Array Nat := .replicate g.size 0
  let mut reached : Array Bool := .replicate g.size false
  let mut queue : Array Nat := #[]
  for r in roots do
    if !reached[r]! then
      reached := reached.set! r true
      queue := queue.push r
  let mut head := 0
  while h : head < queue.size do
    let v := queue[head]
    head := head + 1
    for e in (g.start v)...(g.stop v) do
      let w := g.targets[e]!
      if !reached[w]! then
        reached := reached.set! w true
        pred := pred.set! w (e + 1)
        queue := queue.push w
  let mut edgeSrc : Array Nat := .replicate g.numEdges 0
  for v in 0...g.size do
    for e in (g.start v)...(g.stop v) do
      edgeSrc := edgeSrc.set! e v
  return { pred, edgeSrc, reached }

end Graph

namespace LGraph

/--
Merges repeated edges `v → w` into one whose label is the bitwise or of theirs, keeping first
occurrences in order. Linear: a marker per vertex records where `w`'s edge from the current `v` went.
-/
def dedup (lg : LGraph) : LGraph := Id.run do
  let g := lg.graph
  let n := g.size
  -- `seen[w] = v + 1` if `v`'s edge to `w` is at `slot[w]` in the output
  let mut seen : Array Nat := .replicate n 0
  let mut slot : Array Nat := .replicate n 0
  let mut offsets : Array Nat := .replicate (n + 1) 0
  let mut targets : Array Nat := .emptyWithCapacity g.numEdges
  let mut labels : ByteArray := .emptyWithCapacity g.numEdges
  for v in 0...n do
    for e in (g.start v)...(g.stop v) do
      let w := g.targets[e]!
      let l := lg.labels.get! e
      if seen[w]! == v + 1 then
        let p := slot[w]!
        labels := labels.set! p (labels.get! p ||| l)
      else
        seen := seen.set! w (v + 1)
        slot := slot.set! w targets.size
        targets := targets.push w
        labels := labels.push l
    offsets := offsets.set! (v + 1) targets.size
  return { graph := { offsets, targets }, labels }

end LGraph

end Agitate.ImportGraph
