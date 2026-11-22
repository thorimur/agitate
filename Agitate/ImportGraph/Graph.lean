/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
# Dependency graphs at scale

Label propagation over large dependency graphs (all source declarations of Mathlib, say), without
recursion and without per-step tree-map operations. Vertices are numbered densely, so traversals
use arrays. Graphs may be cyclic (mutual inductives make declaration graphs so): labels propagate
over strongly connected components, found by an iterative Tarjan. Core's `Lean.SCC.scc` recurses,
which overflows the stack at this scale.
-/
module

public section

namespace Agitate.ImportGraph

/-- A directed graph on the vertices `0, …, size - 1`, given by successor lists. -/
structure Graph where
  succs : Array (Array Nat)
deriving Inhabited

namespace Graph

def size (g : Graph) : Nat := g.succs.size

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

end Graph

end Agitate.ImportGraph
