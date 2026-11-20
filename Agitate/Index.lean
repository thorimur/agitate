/-
The olean index: everything `agitate` needs about the imported modules, read directly from each
module's `.olean` parts with `readModuleDataParts`, without `importModules`/`finalizeImport`.

Where this mirrors core behaviour, the core definition (Lean `v4.33.1`) is named in the docstring.
That is the contract the differential checker (`agitate-check`) verifies.
-/
module

public import Lean.Environment
public import Lean.ExtraModUses
public import Lean.Meta.Match.MatcherInfo
import all Lean.Environment          -- `subsumesInfo`
import all Lean.Compiler.MetaAttr    -- `metaExt`, `declMetaExt`
import all Lean.ExtraModUses         -- `extraModUses`, `isExtraRevModUseExt`

open Lean

namespace Agitate

/-- One imported module: its exported (`.olean`) and private (`.olean.private`) parts. -/
public structure Module where
  name : Name
  /-- The `.olean` part. Its constants form the public view (`Environment.setExporting true`). -/
  pub : ModuleData
  /--
  The `.olean.private` part: all constants, imports and extension entries. Shake treats every
  module as `import all`ed, so core's lookups read this part too.
  -/
  priv : ModuleData
  /-- `priv.entries` for the extensions in `Index.extSlots`, in that order (`#[]` if absent). -/
  extEntries : Array (Array EnvExtensionEntry) := #[]
  /--
  A value computed from every constant name and constant object of the module while reading it, in
  parallel. Its only purpose is to fault those pages in concurrently, so that the sequential
  `Index.build` does not page-fault through the regions one at a time on a cold page cache.
  -/
  prefault : UInt64 := 0
deriving Inhabited

/-- The index over the transitive imports of the root modules. -/
public structure Index where
  /-- Modules in `ModuleIdx` order, the order in which `importModulesCore` adds them. -/
  modules : Array Module
  modIdx : Std.HashMap Name ModuleIdx
  /-- As `Kernel.Environment.const2ModIdx`, except without the IR parts' `extraConstNames`. -/
  const2ModIdx : Std.HashMap Name ModuleIdx
  /-- The private constant map built by `finalizeImport` (`Environment.find?` when not exporting). -/
  privConsts : Std.HashMap Name ConstantInfo
  /-- The public constant map built by `finalizeImport` (`(env.setExporting true).find?`). -/
  pubConsts : Std.HashMap Name ConstantInfo
  /-- Names of all imported matchers (the state of `Match.Extension.extension` once loaded). -/
  matchers : Std.HashSet Name
  /--
  As the state of `indirectModUseExt` after `addImportedFn`, but keeping each use's `kind` (the
  attribute that recorded it); see `indirectModUsesExcept`.
  -/
  indirectModUses : Std.HashMap Name (Array (ModuleIdx × String))
  /--
  Names of the extensions whose entries are pre-resolved per module (`Module.extEntries`).
  Looking an extension up among a module's ~40 `entries` compares names structurally, which showed
  up prominently in `calcNeeds` profiles; slot names come from the extension objects themselves, so
  the lookup below usually succeeds on pointer equality.
  -/
  extSlots : Array Name

namespace Index

variable (ix : Index)

public def size : Nat := ix.modules.size
public def modName (i : ModuleIdx) : Name := ix.modules[i]!.name
public def modNames : Array Name := ix.modules.map (·.name)
public def imports (i : ModuleIdx) : Array Import := ix.modules[i]!.priv.imports
/-- All constants of module `i` (`env.header.moduleData[i].constants` in shake). -/
public def constants (i : ModuleIdx) : Array ConstantInfo := ix.modules[i]!.priv.constants
public def getModuleIdx? (mod : Name) : Option ModuleIdx := ix.modIdx[mod]?
public def getModuleIdxFor? (c : Name) : Option ModuleIdx := ix.const2ModIdx[c]?
public def find? (c : Name) : Option ConstantInfo := ix.privConsts[c]?
public def findPublic? (c : Name) : Option ConstantInfo := ix.pubConsts[c]?
public def contains (c : Name) : Bool := ix.privConsts.contains c

/-- The raw extension entries that module `i` stored for the extension named `extName`. -/
public def rawEntries (extName : Name) (i : ModuleIdx) : Array EnvExtensionEntry :=
  match ix.extSlots.idxOf? extName with
  | some slot => ix.modules[i]!.extEntries[slot]!
  | none =>
    match ix.modules[i]!.priv.entries.find? (·.1 == extName) with
    | some (_, es) => es
    | none => #[]

private unsafe def moduleEntriesUnsafe {α β σ : Type} (ix : Index)
    (ext : PersistentEnvExtension α β σ) (i : ModuleIdx) : Array α :=
  unsafeCast (ix.rawEntries ext.name i)

/--
The entries of `ext` stored by module `i`. This is `PersistentEnvExtension.getModuleEntries` in an
environment that imported every module with `import all`, as shake's does.
-/
@[implemented_by moduleEntriesUnsafe]
public opaque moduleEntries {α β σ : Type} (ix : Index) (ext : PersistentEnvExtension α β σ)
    (i : ModuleIdx) : Array α

/-- `isMarkedMeta`, i.e. `metaExt.isTagged`, for imported declarations. -/
public def isMarkedMeta (declName : Name) : Bool :=
  match ix.getModuleIdxFor? declName with
  | some i => (ix.moduleEntries metaExt i).binSearchContains declName Name.quickLt
  | none => false

/-- `isDeclMeta` for an environment with `header.isModule = true`. -/
public def isDeclMeta (declName : Name) : Bool :=
  let inferFor := match declName with
    | .str n "_boxed" => n
    | n               => n
  match ix.getModuleIdxFor? declName with
  | some i => (ix.moduleEntries declMetaExt i).binSearchContains inferFor Name.quickLt
  | none => false

/-- `getExtraModUses`. -/
public def getExtraModUses (i : ModuleIdx) : Array ExtraModUse :=
  ix.moduleEntries extraModUses i

/-- `isExtraRevModUse`. -/
public def isExtraRevModUse (i : ModuleIdx) : Bool :=
  !(ix.moduleEntries isExtraRevModUseExt i).isEmpty

/-- `MapDeclarationExtension.find?` for imported declarations. -/
public def mapFind? {α : Type} [Inhabited α] (ext : MapDeclarationExtension α) (declName : Name) :
    Option α :=
  match ix.getModuleIdxFor? declName with
  | some i =>
    match (ix.moduleEntries ext.toPersistentEnvExtension i).binSearch (declName, default)
        (fun a b => Name.quickLt a.1 b.1) with
    | some e => some e.2
    | none => none
  | none => none

/-- `ParametricAttribute.getParam?` for imported declarations. -/
public def getParam? {α : Type} [Inhabited α] (attr : ParametricAttribute α) (decl : Name) :
    Option α :=
  match ix.getModuleIdxFor? decl with
  | some i =>
    let entries := ix.moduleEntries attr.ext i
    let entry? := if attr.preserveOrder then
      entries.find? (·.1 == decl)
    else
      entries.binSearch (decl, default) (fun a b => Name.quickLt a.1 b.1)
    entry?.map (·.2)
  | none => none

end Index

namespace Index

/-- The indirect module uses whose kind is not ignored, in the shape of `indirectModUseExt`'s state. -/
public def indirectModUsesExcept (ix : Index) (ignore : String → Bool) :
    Std.HashMap Name (Array ModuleIdx) :=
  ix.indirectModUses.fold (init := {}) fun m n uses =>
    let mods := uses.filterMap fun (i, kind) => if ignore kind then none else some i
    if mods.isEmpty then m else m.insert n mods

end Index

/-! ## Loading -/

/-- Touch what `Index.build` touches: name objects (hashes) and constant object headers (reference
counting on insertion reads them; the constructor tag lives in the same header). -/
private def touch (data : ModuleData) (h : UInt64) : UInt64 :=
  let h := data.constNames.foldl (fun h n => h ^^^ n.hash) h
  data.constants.foldl (fun h ci => if ci.isCtor then h + 1 else h) h

/--
Reads `.olean`, `.olean.server` and `.olean.private` of `mod`. The private region points into the
other two, so they are read together; regions are never freed (cf. `leakEnv := true`). A non-module
olean is a single part holding everything (written at the `.private` level); with `allowNonModule`
it serves as both views, otherwise it is rejected as `lake shake` does.
-/
private def readParts (mod : Name) (allowNonModule : Bool) : IO Module := do
  let mFile ← findOLean mod
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {mod} does not exist"
  let pFile := OLeanLevel.private.adjustFileName mFile
  -- Non-`module`s have no `.olean.private`; read only the main part.
  unless (← pFile.pathExists) do
    let parts ← readModuleDataParts #[mFile]
    if let #[(main, _)] := parts then
      if !main.isModule then
        if allowNonModule then
          return { name := mod, pub := main, priv := main, prefault := touch main 0 }
        throw <| .userError "`lake shake` only works with `module`s currently"
    throw <| IO.userError s!"object file '{pFile}' of module {mod} does not exist"
  let parts ← readModuleDataParts #[mFile, OLeanLevel.server.adjustFileName mFile, pFile]
  let #[(pub, _), _, (priv, _)] := parts
    | throw <| .userError s!"failed to read the .olean parts of {mod}"
  return { name := mod, pub, priv, prefault := touch pub (touch priv 0) }

/-- Depth-first post-order over imports, in declaration order: the order in which
`importModulesCore` pushes to `moduleNames`, and hence the `ModuleIdx` order. -/
private partial def postOrder (loaded : Std.HashMap Name Module) (roots : Array Name) :
    Array Module := Id.run do
  let rec visit (mod : Name) : StateM (Std.HashSet Name × Array Module) Unit := do
    if (← get).1.contains mod then
      return
    modify fun (seen, out) => (seen.insert mod, out)
    let m := loaded[mod]!
    for imp in m.priv.imports do
      visit imp.module
    modify fun (seen, out) => (seen, out.push m)
  let ((), (_, out)) := (roots.forM visit).run ({}, #[])
  return out

private def throwAlreadyImported (modules : Array Module) (const2ModIdx : Std.HashMap Name ModuleIdx)
    (modIdx : Nat) (cname : Name) : IO α :=
  throw <| IO.userError s!"import {modules[modIdx]!.name} failed, environment already contains \
    '{cname}' from {modules[const2ModIdx[cname]!.toNat]!.name}"

/-- Reads all modules imported (transitively) by `roots`, in `ModuleIdx` order, using the current
`searchPathRef`. -/
public def readModules (roots : Array Name) (allowNonModule := false) : IO (Array Module) := do
  -- Read level by level over the import DAG, each level in parallel; the order is fixed afterwards.
  let mut loaded : Std.HashMap Name Module := {}
  let mut seen : Std.HashSet Name := {}
  let mut frontier : Array Name := #[]
  for r in roots do
    if !seen.contains r then
      seen := seen.insert r
      frontier := frontier.push r
  while !frontier.isEmpty do
    let tasks ← frontier.mapM fun mod => IO.asTask (readParts mod allowNonModule)
    let mut next := #[]
    for mod in frontier, t in tasks do
      let m ← IO.ofExcept t.get
      loaded := loaded.insert mod m
      for imp in m.priv.imports do
        if !seen.contains imp.module then
          seen := seen.insert imp.module
          next := next.push imp.module
    frontier := next
  return postOrder loaded roots

/--
Builds the index from the modules returned by `readModules`. The constant maps are built exactly as
in `finalizeImport`, including its `subsumesInfo` rule for theorems that several modules realised.
-/
public def Index.build (modules : Array Module) (extraExts : Array Name := #[]) : IO Index := do
  let extSlots := #[metaExt.name, declMetaExt.name, extraModUses.name, isExtraRevModUseExt.name,
    indirectModUseExt.name, Meta.Match.Extension.extension.name] ++ extraExts
  let modules := modules.map fun m => { m with
    extEntries := extSlots.map fun n => (m.priv.entries.find? (·.1 == n)).map (·.2) |>.getD #[] }
  let mut modIdx : Std.HashMap Name ModuleIdx := {}
  for h : i in 0...modules.size do
    modIdx := modIdx.insert modules[i].name i
  let numConsts := modules.foldl (init := 0) (· + ·.priv.constants.size)
  let numPub := modules.foldl (init := 0) (· + ·.pub.constants.size)
  let mut const2ModIdx : Std.HashMap Name ModuleIdx := .emptyWithCapacity numConsts
  let mut privConsts : Std.HashMap Name ConstantInfo := .emptyWithCapacity numConsts
  let mut pubConsts : Std.HashMap Name ConstantInfo := .emptyWithCapacity numPub
  for h : i in 0...modules.size do
    let data := modules[i].priv
    for cname in data.constNames, cinfo in data.constants do
      match privConsts.getThenInsertIfNew? cname cinfo with
      | (cinfoPrev?, privConsts') =>
        privConsts := privConsts'
        if let some cinfoPrev := cinfoPrev? then
          if subsumesInfo privConsts cinfo cinfoPrev then
            privConsts := privConsts.insert cname cinfo
          else if !subsumesInfo privConsts cinfoPrev cinfo then
            throwAlreadyImported modules const2ModIdx i cname
      const2ModIdx := const2ModIdx.insertIfNew cname i
  for m in modules do
    for cname in m.pub.constNames, cinfo in m.pub.constants do
      match pubConsts.getThenInsertIfNew? cname cinfo with
      | (cinfoPrev?, pubConsts') =>
        pubConsts := pubConsts'
        if let some cinfoPrev := cinfoPrev? then
          if subsumesInfo pubConsts cinfo cinfoPrev then
            pubConsts := pubConsts.insert cname cinfo
  let ix : Index := { modules, modIdx, const2ModIdx, privConsts, pubConsts, matchers := {},
                      indirectModUses := {}, extSlots }
  let mut matchers : Std.HashSet Name := {}
  let mut indirectModUses : Std.HashMap Name (Array (ModuleIdx × String)) := {}
  for h : i in 0...modules.size do
    for e in ix.moduleEntries Meta.Match.Extension.extension i do
      matchers := matchers.insert e.name
    for e in ix.moduleEntries indirectModUseExt i do
      indirectModUses := indirectModUses.alter e.declName (·.getD #[] |>.push (i, e.kind))
  return { ix with matchers, indirectModUses }

end Agitate

namespace Agitate

/-- For `--list-indirect-kinds`: each kind of indirect module use with its counts. -/
public def printIndirectKinds (ix : Index) : IO Unit := do
  let mut counts : Std.HashMap String (Nat × Std.HashSet ModuleIdx) := {}
  for (_, uses) in ix.indirectModUses do
    for (i, kind) in uses do
      let (n, ms) := counts.getD kind (0, {})
      counts := counts.insert kind (n + 1, ms.insert i)
  for (kind, n, ms) in counts.toArray.qsort (·.1 < ·.1) do
    IO.println s!"{kind}\t{n} uses\t{ms.size} modules"

/-- `readModules` followed by `Index.build`. -/
public def Index.load (roots : Array Name) (extraExts : Array Name := #[]) : IO Index := do
  Index.build (← readModules roots) extraExts

end Agitate
