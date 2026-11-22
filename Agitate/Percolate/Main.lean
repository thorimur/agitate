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

public import Agitate.Percolate.Imports
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
  /-- The statuses whose items the deletion tool deletes (for the imports after deletion). -/
  delete : Array String := #["unused"]
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
  --delete <STATUS,...>
                   the statuses of the items to be deleted (default `unused`; `none` deletes
                   nothing); the module records give each module's imports after deleting them
  --profile        print per-phase timings to stderr
"

partial def parseArgs (args : Args) : List String → Except String Args
  | [] => .ok args
  | "--profile" :: rest => parseArgs { args with profile := true } rest
  | "--delete" :: ss :: rest =>
    let ss := if ss == "none" then #[] else (ss.splitOn ",").toArray
    if ss.all (["unused", "moduleUse", "candidate"].contains ·) then
      parseArgs { args with delete := ss } rest
    else .error s!"invalid statuses `{",".intercalate ss.toList}` \
      (allowed: unused, moduleUse, candidate, or none)"
  | "--seed" :: n :: rest => parseArgs { args with seeds := args.seeds.push n.toName } rest
  | "--seeds" :: f :: rest => parseArgs { args with seedFiles := args.seedFiles.push f } rest
  | "-o" :: f :: rest => parseArgs { args with output := some f } rest
  | "--scope" :: g :: rest =>
    match Lake.Glob.ofString? g with
    | some g => parseArgs { args with scope := args.scope.push g } rest
    | none => .error s!"invalid glob `{g}`"
  | [opt@"--seed"] | [opt@"--seeds"] | [opt@"-o"] | [opt@"--scope"] | [opt@"--delete"] =>
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
  /-- The statuses of the items to be deleted, which the module records assume. -/
  delete : Array String
deriving ToJson

/-- One project module, after the deletion: its imports, as they would be written. -/
structure ModuleRecord where
  module : Name
  file : Option String
  imports : Array String
  /-- Whether `imports` differ from the current ones (as sets). -/
  importsChanged : Bool
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
  /-- Why the item has its status (absent if `unused`). -/
  why? : Option Why

/-!
Rendering, by hand: deriving `ToJson` builds a `Json` tree (objects are sorted maps) per record,
which dominated the output phase. These render compact JSON with keys in sorted order and absent
optional fields omitted, as `(toJson r).compress` did (checked byte for byte on Mathlib; DESIGN.md).
-/

private def str (acc : String) (s : String) : String := Json.renderString s acc
private def nats (acc : String) (ns : Array Nat) : String := Id.run do
  let mut acc := acc.push '['
  for h : k in 0...ns.size do
    if k > 0 then acc := acc.push ','
    acc := acc ++ toString ns[k]
  return acc.push ']'
private def strs (acc : String) (ss : Array String) : String := Id.run do
  let mut acc := acc.push '['
  for h : k in 0...ss.size do
    if k > 0 then acc := acc.push ','
    acc := str acc ss[k]
  return acc.push ']'
private def pos (acc : String) (p : Position) : String :=
  acc ++ "{\"column\":" ++ toString p.column ++ ",\"line\":" ++ toString p.line ++ "}"

def Why.render (w : Why) (acc : String) : String := Id.run do
  let mut acc := strs (acc ++ "{\"kinds\":") w.kinds
  if let some r := w.rule? then acc := str (acc ++ ",\"rule\":") r
  if let some b := w.sameModule? then acc := acc ++ ",\"sameModule\":" ++ toString b
  if let some s := w.seed? then acc := acc ++ ",\"seed\":" ++ toString s
  if !w.through.isEmpty then acc := strs (acc ++ ",\"through\":") (w.through.map toString)
  if let some u := w.user? then acc := str (acc ++ ",\"user\":") (toString u)
  if let some m := w.userModule? then acc := str (acc ++ ",\"userModule\":") (toString m)
  if let some u := w.uses? then acc := str (acc ++ ",\"uses\":") (toString u)
  return acc.push '}'

def Record.render (r : Record) : String := Id.run do
  let mut acc := "{\"attributeCmds\":["
  for h : k in 0...r.attributeCmds.size do
    let c := r.attributeCmds[k]
    if k > 0 then acc := acc.push ','
    acc := str (acc ++ "{\"decl\":") (toString c.decl)
    acc := str (acc ++ ",\"kind\":") c.kind
    acc := str (acc ++ ",\"module\":") (toString c.module) |>.push '}'
  acc := nats (acc ++ "],\"candidateFor\":") r.candidateFor
  acc := acc ++ ",\"file\":"
  acc := match r.file with | some f => str acc f | none => acc ++ "null"
  acc := str (acc ++ ",\"module\":") (toString r.module)
  acc := nats (acc ++ ",\"moduleUseFor\":") r.moduleUseFor
  acc := strs (acc ++ ",\"names\":") (r.names.map toString)
  acc := acc ++ ",\"range\":"
  acc := match r.range with
    | some rg => (pos (pos (acc ++ "{\"end\":") rg.«end» ++ ",\"start\":") rg.start).push '}'
    | none => acc ++ "null"
  acc := str (acc ++ ",\"status\":") r.status
  acc := nats (acc ++ ",\"usedBy\":") r.usedBy
  if let some w := r.why? then acc := w.render (acc ++ ",\"why\":")
  return acc.push '}'

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
      #[declRangeExt.toPersistentEnvExtension.name, backwardDefeqAttr.ext.name,
        regularInitAttr.ext.name])
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
  let whys ← timed "why (parallel)" <| IO.lazyPure fun _ => res.whys refs a seedIds
  let deleted (v : Nat) : Bool := args.delete.contains (res.status v).toString
  let isToolchain := ix.modNames.map fun m => (r.ws.findTargetModule? m).isNone
  let imports ← timed "imports after deletion" <| importsAfter refs a (res.declNeedsOf refs) isToolchain deleted args.profile
  timed "output" do
    out.putStrLn (toJson ({ seeds := seedNames, delete := args.delete } : Header)).compress
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
          usedBy := (res.reachAt 0 v).toArray
          candidateFor := (res.reachAt 1 v \ res.reachAt 0 v).toArray
          moduleUseFor := (res.reachAt 2 v \ res.reachAt 1 v).toArray
          attributeCmds
          why? := whys[v]! }
        out.putStrLn rec_.render
    for i in 0...ix.size do
      let mod := ix.modName i
      let some imps := imports[i]! | continue
      if !(args.scope.isEmpty || args.scope.any (·.matches mod)) then continue
      let isModule := ix.modules[i]!.priv.isModule
      let now := importStrings (ix.imports i) isModule
      let after := importStrings imps isModule
      let rec_ : ModuleRecord := {
        module := mod, file := (← r.source? mod).map (·.toString), imports := after
        importsChanged := !(now.all after.contains && after.all now.contains) }
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
