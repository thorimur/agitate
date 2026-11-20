/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

public import Lake.Load.Workspace
public import Lake.Config.Workspace
public import Lake.Config.LeanExe
public import Lake.Config.InstallPath
public import Lake.Config.Env
import Lake.Util.IO

/-!
Module resolution through the Lake workspace (Thomas's decision, DESIGN.md "Module-name shadowing
across packages"). `LEAN_PATH` and `LEAN_SRC_PATH` are not used: a `require`d package earlier on
those paths can shadow the root package's own modules (Lake puts dependencies first). Instead, the
workspace in the working directory is loaded as Lake loads it, and a module is resolved as Lake's
builds resolve it: the workspace's packages, root first, then the toolchain.
-/

public section

open Lean System

namespace Agitate

/-- Resolves module names to their `.olean` and source files. -/
structure Resolver where
  ws : Lake.Workspace
  lean : Lake.LeanInstall
  lake : Lake.LakeInstall

/--
Loads the Lake workspace in `dir`, as `lake` would (without updating dependencies). Lean is the
installation the project's `lean` resolves to (`LEAN_SYSROOT` or `lean --print-prefix`), and Lake
is the one shipped with it. `findLakeInstall?` would look next to *this* executable instead.
-/
def Resolver.load (dir : FilePath := ".") : IO Resolver := do
  let some lean ← Lake.findLeanInstall?
    | throw <| .userError "could not find a Lean installation (`lean` on PATH, or LEAN_SYSROOT)"
  let lake := Lake.LakeInstall.ofLean lean
  let env ← match ← (Lake.Env.compute lake lean (← Lake.findElanInstall?)).toBaseIO with
    | .ok env => pure env
    | .error e => throw <| .userError s!"invalid Lake environment: {e}"
  let some wsDir ← Lake.resolvePath? dir
    | throw <| .userError s!"workspace directory '{dir}' does not exist"
  let some ws ← (Lake.loadWorkspace { lakeEnv := env, wsDir }).toBaseIO
    | throw <| .userError s!"failed to load the Lake workspace in '{wsDir}'"
  return { ws, lean, lake }

/--
The main `.olean` of `mod` and its source file (if found), resolved like Lake does. First, the
module of the workspace's packages, root first (`Workspace.findTargetModule?`, which covers library
modules and executable roots). Otherwise, the toolchain's modules (`Init`, `Std`, `Lean`, `Lake`).
-/
def Resolver.find? (r : Resolver) (mod : Name) : IO (Option (FilePath × Option FilePath)) := do
  if let some m := r.ws.findTargetModule? mod then
    return some (m.oleanFile, some m.leanFile)
  let olean := modToFilePath r.lean.leanLibDir mod "olean"
  if ← olean.pathExists then
    for srcDir in [r.lean.srcDir, r.lake.srcDir] do
      let src := modToFilePath srcDir mod "lean"
      if ← src.pathExists then
        return some (olean, some src)
    return some (olean, none)
  return none

/-- The main `.olean` of `mod`; throws if no package or the toolchain provides it. -/
def Resolver.olean (r : Resolver) (mod : Name) : IO FilePath := do
  let some (olean, _) ← r.find? mod
    | throw <| .userError s!"unknown module '{mod}': not provided by any package of the workspace \
        or by the toolchain"
  return olean

/-- The source file of `mod`, if known. -/
def Resolver.source? (r : Resolver) (mod : Name) : IO (Option FilePath) := do
  return (← r.find? mod).bind (·.2)

/-- The root modules of the root package's default targets (what `lake shake` checks by default). -/
def Resolver.defaultRoots (r : Resolver) : Array Name :=
  r.ws.defaultTargetRoots

end Agitate
