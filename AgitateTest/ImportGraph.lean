/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/- Tests of `Agitate.ImportGraph`; building this file runs them. -/
import Agitate.ImportGraph
import Lean.Data.DeclarationRange

open Agitate.ImportGraph

/-- `0 → 1 ⇄ 2 → 3`; `4 → 0` is not reachable from `0`. -/
def g : Graph := .ofSuccs #[#[1], #[2], #[1, 3], #[], #[0]]

-- components come after everything they reach; the cycle is one component
#guard (g.components #[0]).comps == #[#[3], #[2, 1], #[0]]
#guard (g.components #[0]).compOf == #[3, 2, 2, 1, 0]
#guard (g.components #[4]).comps == #[#[3], #[2, 1], #[0], #[4]]

def single (v : Nat) : Bitset := {v}

-- forwards: who reaches `v`; the cycle's members share their label
#guard (g.flowForward #[0] single).map (·.toArray) == #[#[0], #[0, 1, 2], #[0, 1, 2], #[0, 1, 2, 3], #[]]
-- only `init` of reached vertices counts
#guard (g.flowForward #[1] single).map (·.toArray) == #[#[], #[1, 2], #[1, 2], #[1, 2, 3], #[]]

-- a long chain: no recursion, so no stack overflow (only the root is labelled: `{v}` takes `v/8`
-- bytes, so labelling every vertex would be quadratic in space)
def chain (n : Nat) : Graph := .ofSuccs <| (Array.range n).map fun i => if i + 1 < n then #[i + 1] else #[]
def root0 (v : Nat) : Bitset := if v == 0 then {0} else ∅
#guard ((chain 100000).flowForward #[0] root0)[99999]!.toArray == #[0]
#guard ((chain 100000).components #[0]).comps.size == 100000

-- edge lists: a counting sort keeps each vertex's edges in input order, labels alongside
def lg := Graph.ofEdgesL 3 #[2, 0, 2, 0, 0] #[0, 1, 1, 1, 2] ⟨#[1, 2, 4, 8, 16]⟩
#guard lg.graph.succs 0 == #[1, 1, 2] && lg.graph.succs 1 == #[] && lg.graph.succs 2 == #[0, 1]
#guard lg.labels.data == #[2, 8, 16, 1, 4]
-- deduplication or-s the labels of repeated edges
#guard lg.dedup.graph.succs 0 == #[1, 2] && lg.dedup.labels.data == #[10, 16, 1, 4]

-- breadth-first search: shortest paths, edge sources
def t := g.bfs #[0]
#guard t.reached == #[true, true, true, true, false]
#guard t.pred[3]! != 0 && t.edgeSrc[t.pred[3]! - 1]! == 2

-- need kinds
open Agitate.ImportGraph.NeedKinds in
#guard (type ||| regenerated).toNames == #["type", "regenerated"] && (type ||| value).has value

-- range groups: nested ranges join the enclosing one, in source order
open Lean in
def rng (l₁ c₁ l₂ c₂ : Nat) : DeclarationRange :=
  { pos := ⟨l₁, c₁⟩, charUtf16 := c₁, endPos := ⟨l₂, c₂⟩, endCharUtf16 := c₂ }
def groups := groupRanges #[(`B.x, rng 2 2 2 9), (`C, rng 5 0 6 0), (`B, rng 1 0 3 0),
  (`B.y, rng 3 0 4 0)]
#guard groups.members == #[#[`B, `B.x], #[`B.y], #[`C]]
#guard groups.groupOf[`B.x]? == some 0 && groups.groupOf[`C]? == some 2


-- imports compose: a public import passes on what arrives publicly
open ImportKind in
#guard pub.andThen? priv == some priv && priv.andThen? pub == none && pub.andThen? metaPub == some metaPub
-- `import all` passes on what arrives privately, and keeps privacy
open ImportKind in
#guard priv.andThen? all == some priv && all.andThen? all == some all

-- a chain 0 ← 1 ← 2 of public imports: importing 2 publicly provides 0, so needs on 0 and 2 reduce
-- to one import of 2
def chainH : Hierarchy := Id.run do
  let mut h : Hierarchy := #[]
  for i in 0...3 do
    h := h.push (h.provides i (if i == 0 then #[] else #[(i - 1, .pub)]))
  return h
def chainNeeds : ImportNeeds := ({} : ImportNeeds).insert { isExported := true } 0
  |>.insert { isExported := true } 2
#guard (chainNeeds.reduce chainH).toArray.map (fun (k, i) => (k.toImportString, i)) == #[("public import", 2)]
-- a phased meta need is not met by a plain import
def metaNeeds : ImportNeeds := ({} : ImportNeeds).insert { isExported := false, isMeta? := some true } 0
#guard (metaNeeds.reduce chainH).toArray.map (fun (k, i) => (k.toImportString, i)) == #[("meta import", 0)]

-- stances: public meta code using runtime code needs a public meta import; a theorem's proof only
-- a private, phaseless one
open NeedKinds in
#guard ({ isPublic := true, phase := .meta } : Stance).importNeeds (value ||| code)
    { isPublic := true, phase := .runtime } ==
  #[{ isExported := false }, { isExported := true, isMeta? := some true }]
open NeedKinds in
#guard ({ isPublic := true } : Stance).importNeeds value { isPublic := true } == #[{ isExported := false }]
-- runtime code needs even a constructor without `meta`
open NeedKinds in
#guard ({ isPublic := false, phase := .runtime } : Stance).importNeeds code { isPublic := true } ==
  #[{ isExported := false, isMeta? := some false }]
