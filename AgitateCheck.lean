/-
`agitate-check`: verifies the olean index against a real environment loaded the way `lake shake` loads
it (`importModulesCore` + `finalizeImport (loadExts := false)`).

  lake env .lake/build/bin/agitate-check <MODULE>...

Every query `agitate` answers from the index is compared with core's answer on that environment, for
every imported constant: module order and imports, `getModuleIdxFor?`, the private and public constant
views, `isMarkedMeta`/`isDeclMeta`, extra (reverse) module uses, indirect module uses, and
reserved-ness in both semantics (upstream; and fixed, with `mainModule` set and the matcher
extension loaded). It also checks that core registers exactly as many reserved-name predicates as
`Agitate.Reserved` ports.
-/
import Agitate
import Lean.Meta.Match.MatcherInfo

open Lean Agitate

/--
Fills the state of the matcher-info extension from its imported entries. `lake shake` imports with
`loadExts := false`, so `isMatcherCore` sees no imported matchers; this gives the reference for
agitate's fixed reserved-name semantics.
-/
def initMatcherExt (env : Environment) : IO Environment := do
  let ext := Meta.Match.Extension.extension
  let is := ext.toEnvExtension.getState env
  let newState ← ext.addImportedFn is.importedEntries { env := env, opts := {} }
  return ext.toEnvExtension.setState (asyncMode := .sync) env { is with state := newState }

structure Report where
  checks : Nat := 0
  failures : Std.HashMap String (Nat × Array String) := {}

def Report.check (r : Report) (what : String) (ok : Bool) (example_ : Unit → String) : Report :=
  let r := { r with checks := r.checks + 1 }
  if ok then r else
  let (n, exs) := r.failures.getD what (0, #[])
  { r with failures := r.failures.insert what (n + 1, if exs.size < 5 then exs.push (example_ ()) else exs) }

def main (args : List String) : IO UInt32 := do
  let mods := args.toArray.map (·.toName)
  if mods.isEmpty then
    IO.eprintln "usage: agitate-check <MODULE>..."
    return 2
  initSearchPath (← findSysroot)

  -- the reference: shake's environment
  let imps := mods.map ({ module := · })
  let (_, s) ← (importModulesCore imps (isExported := true)).run
  let env ← finalizeImport s.markAllExported (isModule := true) imps {} (leakEnv := true) (loadExts := false)
  let is := indirectModUseExt.toEnvExtension.getState env
  let st ← indirectModUseExt.addImportedFn is.importedEntries { env := env, opts := {} }
  let env := indirectModUseExt.toEnvExtension.setState (asyncMode := .sync) env { is with state := st }
  let envFixed ← initMatcherExt env

  let ix ← Index.load mods Reserved.extNames
  let mut r : Report := {}

  let numPreds := (← reservedNamePredicatesRef.get).size
  r := r.check "number of reserved-name predicates" (numPreds == Reserved.numPredicates)
    fun _ => s!"core registers {numPreds}, agitate ports {Reserved.numPredicates}"
  r := r.check "module order" (env.header.moduleNames == ix.modNames)
    fun _ => s!"{env.header.moduleNames.size} vs {ix.modNames.size} modules"
  if env.header.moduleNames != ix.modNames then
    IO.eprintln "module order differs; skipping the remaining checks"
    return 1

  let pubEnv := env.setExporting true
  let upstream : Reserved.Ctx := { ix, upstream := true }
  let fixed : Reserved.Ctx := { ix, upstream := false }
  for h : i in 0...env.header.moduleData.size do
    let data := env.header.moduleData[i]
    let modName := ix.modName i
    r := r.check "imports" (data.imports == ix.imports i) fun _ => s!"{modName}"
    r := r.check "constant names" (data.constNames == (ix.constants i).map (·.name)) fun _ => s!"{modName}"
    r := r.check "extra mod uses" (getExtraModUses env i == ix.getExtraModUses i) fun _ => s!"{modName}"
    r := r.check "extra rev mod use" (isExtraRevModUse env i == ix.isExtraRevModUse i) fun _ => s!"{modName}"
    let modEnv := envFixed.setMainModule modName
    for c in data.constNames do
      r := r.check "getModuleIdxFor?" (env.getModuleIdxFor? c == ix.getModuleIdxFor? c) fun _ => s!"{c}"
      r := r.check "find? (private view)"
        ((env.find? c).map (·.name) == (ix.find? c).map (·.name)) fun _ => s!"{c}"
      r := r.check "find? (public view)"
        ((pubEnv.find? c).map (fun ci => (ci.name, ci.hasValue (allowOpaque := true))) ==
          (ix.findPublic? c).map (fun ci => (ci.name, ci.hasValue (allowOpaque := true)))) fun _ => s!"{c}"
      r := r.check "isMarkedMeta" (isMarkedMeta env c == ix.isMarkedMeta c) fun _ => s!"{c}"
      r := r.check "isDeclMeta" (isDeclMeta env c == ix.isDeclMeta c) fun _ => s!"{c}"
      r := r.check "reserved (upstream)" (isReservedName env c == Reserved.isReserved upstream c)
        fun _ => s!"{c}: core {isReservedName env c}"
      r := r.check "reserved (fixed)" (isReservedName modEnv c == Reserved.isReserved fixed c)
        fun _ => s!"{c}: core {isReservedName modEnv c}"

  let coreIndirect := indirectModUseExt.getState env
  r := r.check "indirect mod uses"
    (let ours := ix.indirectModUsesExcept (fun _ => false)
     coreIndirect.size == ours.size && coreIndirect.toList.all fun (n, ms) => ours[n]? == some ms)
    fun _ => s!"{coreIndirect.size} vs {ix.indirectModUses.size} entries"

  IO.println s!"{r.checks} checks over {ix.size} modules, {env.constants.map₁.size} constants"
  if r.failures.isEmpty then
    IO.println "all checks passed"
    return 0
  for (what, n, exs) in r.failures.toList do
    IO.println s!"FAILED {what}: {n} mismatches, e.g. {exs}"
  return 1
