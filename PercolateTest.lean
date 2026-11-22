/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/- Tests of `Percolate`; building this file runs them. -/
import Percolate
import Lean.Elab.Command

open Lean Percolate

/-- `0 → 1 ⇄ 2 → 3`; `4 → 0` is not reachable from `0`. -/
def g : Graph := ⟨#[#[1], #[2], #[1, 3], #[], #[0]]⟩

-- components come after everything they reach; the cycle is one component
#guard (g.components #[0]).comps == #[#[3], #[2, 1], #[0]]
#guard (g.components #[0]).compOf == #[3, 2, 2, 1, 0]
#guard (g.components #[4]).comps == #[#[3], #[2, 1], #[0], #[4]]

def single (v : Nat) : Bitset := {v}

-- forwards: who reaches `v`; the cycle's members share their label
#guard (g.flowForward #[0] single).map (·.toArray) == #[#[0], #[0, 1, 2], #[0, 1, 2], #[0, 1, 2, 3], #[]]
-- only `init` of reached vertices counts
#guard (g.flowForward #[1] single).map (·.toArray) == #[#[], #[1, 2], #[1, 2], #[1, 2, 3], #[]]
-- backwards: what `v` reaches
#guard (g.flowBackward #[0] single).map (·.toArray) == #[#[0, 1, 2, 3], #[1, 2, 3], #[1, 2, 3], #[3], #[]]

-- a long chain: no recursion, so no stack overflow (only the root is labelled: `{v}` takes `v/8`
-- bytes, so labelling every vertex would be quadratic in space)
def chain (n : Nat) : Graph := ⟨(Array.range n).map fun i => if i + 1 < n then #[i + 1] else #[]⟩
def root0 (v : Nat) : Bitset := if v == 0 then {0} else ∅
#guard ((chain 100000).flowForward #[0] root0)[99999]!.toArray == #[0]
#guard ((chain 100000).flowBackward #[0] root0)[0]!.toArray == #[0]
#guard ((chain 100000).components #[0]).comps.size == 100000

def ex := Graph.explore #["a"] fun
  | "a" => #["b", "c"] | "b" => #["c"] | "c" => #["a"] | _ => #[]
#guard ex.verts == #["a", "b", "c"]
#guard ex.graph.succs == #[#[1, 2], #[2], #[0]]
#guard ex.index["c"]? == some 2

run_cmd do
  let env ← getEnv
  let used := transitivelyUsedConstants env #[``Nat.add_comm]
  unless used[0]? == some ``Nat.add_comm && used.contains ``Nat.add do
    throwError "transitivelyUsedConstants: {used}"
  let req := (transitivelyRequiredModules env #[`Percolate.Graph])[`Percolate.Graph]!
  unless req.contains `Init.Prelude && req.contains `Percolate.Graph
      && !req.contains `Percolate.Environment do
    throwError "transitivelyRequiredModules: {req}"
