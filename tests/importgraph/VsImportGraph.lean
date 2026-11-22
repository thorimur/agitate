/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
Differential test: `Agitate.ImportGraph.Environment` against ImportGraph's own functions on the same
environment (run by `scripts/test-percolate.sh` with an ImportGraph build on `LEAN_PATH`).
-/
import ImportGraph.Imports.RequiredModules
import Agitate.ImportGraph.Environment
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames.filter fun m =>
    (`ImportGraph).isPrefixOf m || (`Agitate.ImportGraph).isPrefixOf m || (`Lean.Util).isPrefixOf m
  let theirs ← liftCoreM <| env.transitivelyRequiredModules' mods.toList
  let ours := Agitate.ImportGraph.transitivelyRequiredModules env mods
  for m in mods do
    let t := (theirs.find? m).getD {}
    let o := ours[m]?.getD #[]
    unless t.size == o.size && o.all t.contains do
      throwError "transitivelyRequiredModules differ on {m}: {t.toList} vs {o}"
  logInfo m!"transitivelyRequiredModules: identical on {mods.size} modules"
  let roots := #[``Lean.Name.transitivelyUsedConstants, ``Agitate.ImportGraph.Graph.flowForward,
    ``Lean.Environment.transitivelyRequiredModules', ``Nat.add_comm]
  for r in roots do
    let t ← liftCoreM <| r.transitivelyUsedConstants
    let o := Agitate.ImportGraph.transitivelyUsedConstants env #[r]
    unless t.size == o.size && o.all t.contains do
      throwError "transitivelyUsedConstants differ on {r}: {t.size} vs {o.size}"
    logInfo m!"transitivelyUsedConstants {r}: identical ({o.size} constants)"
