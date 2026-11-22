/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Thomas Murrills
-/

/-
# ImportGraph's constant dependencies on `Percolate.Graph`

Ported from ImportGraph (`ImportGraph/Imports/RequiredModules.lean`,
leanprover-community/import-graph at `16f02aa`): `NameSet.transitivelyUsedConstants` and
`Environment.transitivelyRequiredModules'`, with the same results. Changes: the traversals are
`Graph.explore` and `Graph.flowBackward`, module sets are `Percolate.Bitset`s instead of `BitVec N`,
and results are arrays (`transitivelyUsedConstants` in discovery order, not sorted). Constants that
are not in the environment have no successors here; ImportGraph's `getConstInfo` throws.
-/
module

public import Lean.Environment
public import Lean.Util.FoldConsts
public import Percolate.Bitset
public import Percolate.Graph

public section

open Lean

namespace Percolate

/-- The constants `ci` uses: those of `ConstantInfo.getUsedConstantsAsSet`, as ImportGraph uses. -/
def usedConstants (ci : ConstantInfo) : Array Name :=
  ci.getUsedConstantsAsSet.foldl (·.push ·) #[]

/-- The constant-use graph of `env` from `roots`. -/
def exploreConstants (env : Environment) (roots : Array Name) : Graph.Explored Name :=
  Graph.explore roots fun c => (env.find? c).map usedConstants |>.getD #[]

/--
The constants that `roots` use, transitively, `roots` included (ImportGraph's
`NameSet.transitivelyUsedConstants`).
-/
def transitivelyUsedConstants (env : Environment) (roots : Array Name) : Array Name :=
  (exploreConstants env roots).verts

/--
For each module in `modules`, the modules declaring the constants that its non-internal constants
use, transitively (ImportGraph's `Environment.transitivelyRequiredModules'`). As there
(`Environment.getModuleFor?`), constants of the environment's own main module count as declared in
`env.header.mainModule`.
-/
def transitivelyRequiredModules (env : Environment) (modules : Array Name) :
    Std.HashMap Name (Array Name) := Id.run do
  let numMods := env.header.moduleNames.size
  let modOf? (c : Name) : Option Nat :=
    match env.getModuleIdxFor? c with
    | some i => some i.toNat
    | none => if env.constants.map₂.contains c then some numMods else none
  let modName (i : Nat) : Name := env.header.moduleNames[i]?.getD env.header.mainModule
  let rootsOf (m : Name) : Array Name :=
    match env.getModuleIdx? m with
    | some i => env.header.moduleData[i.toNat]!.constNames.filter (!·.isInternal)
    | none => #[]
  let ex := exploreConstants env (modules.flatMap rootsOf)
  let init (v : Nat) : Bitset := ex.graph.succs[v]!.foldl (init := ∅) fun s w =>
    match modOf? ex.verts[w]! with
    | some i => s.insert i
    | none => s
  let labels := ex.graph.flowBackward (Array.range ex.verts.size) init
  let mut out := {}
  for m in modules do
    let r := (rootsOf m).foldl (init := (∅ : Bitset)) fun r n => r ∪ labels[ex.index[n]!]!
    out := out.insert m (r.toArray.map modName)
  return out

end Percolate
