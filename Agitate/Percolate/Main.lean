/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/

/-
`percolate`: which source items of a project given declarations (seeds) need, for a tool that
deletes the rest. Output is JSON Lines: a header, then one record per item (`Record`).
-/
module

public import Agitate.Percolate.Needs
public import Agitate.Workspace
public import Lake.Config.Glob
public import Lean.Data.Json.FromToJson.Basic
import Lake.Load.Toml  -- `Lake.Glob.ofString?`

public section

open Lean Agitate.ImportGraph

namespace Agitate.Percolate

structure Args where
  seeds : Array Name := #[]
  seedFiles : Array System.FilePath := #[]
  /-- Report only items of modules matching one of these (all project modules if empty). -/
  scope : Array Lake.Glob := #[]
  output : Option System.FilePath := none
  profile : Bool := false
  /-- Root modules to load (default: the root package's default targets). -/
  mods : Array Name := #[]

def usage : String := "percolate: which source declarations of a project given declarations need

USAGE:
  percolate [OPTIONS] (--seed <NAME> | --seeds <FILE>)... [MODULE...]

Run in the workspace's root directory. Loads the MODULEs (default: the root package's default
targets) and their imports through the Lake workspace. The project is the root package's modules;
items of other packages are never reported. Writes JSON Lines: a header with the seeds, then one
record per source item, with its file, full declaration range, names, status (needed, candidate,
moduleUse or unused) and the seeds that need it. See README.md.

OPTIONS:
  --seed <NAME>    a declaration whose needs to find (repeatable)
  --seeds <FILE>   read seed declarations from FILE, one name per line
  --scope <GLOB>   report only items of modules matching GLOB (repeatable; Lake globs: `Foo`,
                   `Foo.*` for `Foo` and its submodules, `Foo.+` for its submodules only)
  -o <FILE>        write to FILE instead of stdout
  --profile        print per-phase timings to stderr
"

partial def parseArgs (args : Args) : List String → Except String Args
  | [] => .ok args
  | "--profile" :: rest => parseArgs { args with profile := true } rest
  | "--seed" :: n :: rest => parseArgs { args with seeds := args.seeds.push n.toName } rest
  | "--seeds" :: f :: rest => parseArgs { args with seedFiles := args.seedFiles.push f } rest
  | "-o" :: f :: rest => parseArgs { args with output := some f } rest
  | "--scope" :: g :: rest =>
    match Lake.Glob.ofString? g with
    | some g => parseArgs { args with scope := args.scope.push g } rest
    | none => .error s!"invalid glob `{g}`"
  | [opt@"--seed"] | [opt@"--seeds"] | [opt@"-o"] | [opt@"--scope"] =>
    .error s!"missing argument to `{opt}`"
  | arg :: rest =>
    if arg.startsWith "-" then .error s!"unknown option `{arg}`"
    else parseArgs { args with mods := args.mods.push arg.toName } rest

/-- A full declaration range: from `start` to `end` (exclusive), lines from 1, columns from 0 in
codepoints (`Lean.Position`). -/
structure RangeOut where
  start : Position
  «end» : Position
deriving ToJson

/-- An `attribute [kind] decl` command in `module` (another module than the declaration's). -/
structure AttrCmd where
  module : Name
  kind : String
  decl : Name
deriving ToJson

/-- The header line. -/
structure Header where
  format : String := "percolate/1"
  /-- The seeds; records refer to them by index. -/
  seeds : Array Name
deriving ToJson

/-- One source item. -/
structure Record where
  module : Name
  file : Option String
  /-- `none` for constants without a declaration range (nothing to delete by range). -/
  range : Option RangeOut
  /-- Declarations of the item as written or derived in the source (private names unmangled). -/
  names : Array Name
  status : String
  /-- Seeds that need the item through recorded needs (`needed`). -/
  usedBy : Array Nat
  /-- Further seeds that may need it through unrecorded uses of its kind (`candidate`). -/
  candidateFor : Array Nat
  /-- Further seeds that may need it only through module-level uses (`moduleUse`). -/
  moduleUseFor : Array Nat
  /-- `attribute` commands on the item's declarations in other modules: to delete with it. -/
  attributeCmds : Array AttrCmd
deriving ToJson

/-- Import closure of `roots`, ascending. -/
def importClosure (ix : Index) (roots : Array ModuleIdx) : Array ModuleIdx := Id.run do
  let mut seen : Bitset := ∅
  let mut todo := roots
  while let some i := todo.back? do
    todo := todo.pop
    if seen.has i then continue
    seen := seen.insert i
    for imp in ix.imports i do
      if let some j := ix.getModuleIdx? imp.module then
        if !seen.has j then todo := todo.push j
  return seen.toArray

def run (args : Args) (r : Resolver) : IO UInt32 := do
  let timed {α} (phase : String) (act : IO α) : IO α := do
    if !args.profile then act else
    let t0 ← IO.monoMsNow
    let a ← act
    IO.eprintln s!"[profile] {phase}: {(← IO.monoMsNow) - t0} ms"
    return a
  let mut seedNames := args.seeds
  for f in args.seedFiles do
    for l in (← IO.FS.lines f) do
      let l := l.trimAscii.copy
      if !l.isEmpty then seedNames := seedNames.push l.toName
  if seedNames.isEmpty then
    IO.eprintln s!"error: no seeds given\n\n{usage}"
    return 2
  let modules ← timed "readModules" <| readModules r.olean args.mods (allowNonModule := true)
  let ix ← timed "Index.build" <|
    Index.build modules (Reserved.extNames ++
      #[declRangeExt.toPersistentEnvExtension.name, backwardDefeqAttr.ext.name])
  let refs : RefCtx := { ix, reserved := { ix, upstream := false }, reservedRefsToBase := true,
                         indirectModUses := {}, implementedByNeeds := true,
                         resolveDuplicates := true, preresolvedNeeds := true }
  let isProject := ix.modNames.map (r.ws.root.isLocalModule ·)
  let a ← timed "items (parallel)" <| analyse refs isProject
  let mut seedIds := #[]
  let mut seedMods := #[]
  for s in seedNames do
    let decls := ix.dupDecls[s]?.getD (ix.getModuleIdxFor? s |>.toArray) |>.filter (isProject[·]!)
    if decls.isEmpty then
      IO.eprintln s!"error: seed `{s}` is not a declaration of the project's loaded modules"
      return 2
    seedMods := seedMods ++ decls
    seedIds := seedIds.push <| decls.filterMap fun j => (a.items[j]!.constItem[s]?).map a.globalId
  let closure := importClosure ix seedMods |>.filter (isProject[·]!)
  let res ← percolate refs a closure seedIds args.profile
  let out ← match args.output with
    | some p => do pure (IO.FS.Stream.ofHandle (← IO.FS.Handle.mk p .write))
    | none => IO.getStdout
  timed "output" do
    out.putStrLn (toJson ({ seeds := seedNames } : Header)).compress
    for i in 0...ix.size do
      let mod := ix.modName i
      if !isProject[i]! || !(args.scope.isEmpty || args.scope.any (·.matches mod)) then continue
      let file := (← r.source? mod).map (·.toString)
      for (item, k) in a.items[i]!.items.zipIdx do
        let v := a.offset[i]! + k
        let attributeCmds := item.names.flatMap fun c =>
          (ix.indirectModUses[c]?.getD #[]).map fun (j, kind) =>
            { module := ix.modName j, kind, decl := c : AttrCmd }
        let rec_ : Record := {
          module := mod, file
          range := item.range.map fun r => { start := r.pos, «end» := r.endPos }
          names := item.names.map privateToUserName
          status := (res.status v).toString
          usedBy := res.needed[v]!.toArray
          candidateFor := (res.candidate[v]! \ res.needed[v]!).toArray
          moduleUseFor := (res.moduleUse[v]! \ res.candidate[v]!).toArray
          attributeCmds }
        out.putStrLn (toJson rec_).compress
    out.flush
  return 0

/-- The `main` of `percolate`. -/
def main (argv : List String) : IO UInt32 := do
  if argv.contains "--help" || argv.contains "-h" then
    IO.println usage
    return 0
  let args ← match parseArgs {} argv with
    | .ok args => pure args
    | .error e => IO.eprintln s!"error: {e}\n\n{usage}"; return 2
  let r ← Resolver.load
  let args := if args.mods.isEmpty then { args with mods := r.defaultRoots } else args
  if args.mods.isEmpty then
    IO.eprintln s!"error: no modules specified and there are no applicable default targets\n\n{usage}"
    return 2
  run args r

end Agitate.Percolate
