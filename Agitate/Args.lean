/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Ullrich, Thomas Murrills
-/

/-
Command-line arguments and the shared CLI driver of `agitate` (module system) and
`agitate-nonmodule` (non-module code). The option fields come from upstream `Lake.Shake.Args`
(Lean `v4.33.1`), extended by agitate's options.
-/
module

public import Lean.Util.Path
public import Agitate.Workspace
public import Lake.Config.Glob
import Lake.Load.Toml

public section

open Lean

namespace Agitate

/-- The parsed CLI arguments, shared by `agitate` and `agitate-nonmodule`. -/
structure Args where
  /-- Print per-phase wall-clock timings to stderr (`agitate` addition). -/
  profile : Bool := false
  /-- Only print the kinds of indirect module uses with their counts, then exit (`agitate` addition). -/
  listIndirectKinds : Bool := false
  /--
  Compute reserved names exactly as `lake shake` v4.33.1 does, including its two quirks
  (`Agitate.Reserved`). Used for the strict parity test (`agitate` addition).
  -/
  upstreamReserved : Bool := false
  /--
  Count a reference to a reserved name as a reference to the declaration it is regenerated from
  (`Reserved.reservedBase?`). `false` (`--ignore-reserved-refs`) drops such references, as
  `lake shake` does (`agitate` addition; Thomas's decision, DESIGN.md "Reserved names").
  -/
  reservedRefsToBase : Bool := true
  /--
  Kinds (attribute names) of indirect module uses to ignore; `*` ignores all. Upstream counts all
  (`agitate` addition, DESIGN.md "Indirect module uses").
  -/
  ignoreIndirectKinds : Array String := #[]
  /--
  Count an indirect module use when the module reaches the recording module through an import of the
  same or a *stronger* (public) kind, as everywhere else in shake. Upstream checks only the same kind,
  so a private use of a declaration whose attribute module is imported publicly is dropped, and the
  `--fix` result fails to build (`tests/fixture/Fixture/InstUse.lean`). `false`
  (`--upstream-indirect`) restores the upstream check (`agitate` addition, DESIGN.md).
  -/
  indirectViaPublic : Bool := true
  /--
  Count the target of `@[implemented_by g] def f` as needed by `f`'s module. Nothing records it, so
  upstream removes the import providing `g`, and the `--fix` result fails to build. `false`
  (`--ignore-implemented-by`) restores upstream behaviour (`agitate` addition, DESIGN.md
  "Known blind spots").
  -/
  implementedByNeeds : Bool := true
  /--
  For a name declared in several modules (theorems identical up to binder annotations), charge a
  reference to the module itself if it declares the name, else to the declarer whose copy the
  module's environment showed (the last loaded, by core's rule). Upstream charges the first
  declarer, which can add an import from outside the closure, or keep a copy that elaborates
  differently (`Resolved.forModule`).
  `false` (`--upstream-duplicates`) restores upstream behaviour (`agitate` addition).
  -/
  resolveDuplicates : Bool := true
  /--
  Count a name that a syntax quotation preresolved (`` `(foo) `` in a `macro`, elaborator, …) as
  an extra module use of its declaring module: non-meta, public if the declaration containing the
  quotation is. Lean records nothing for it, so upstream removes an import used only that way, and
  every expansion of the quotation then fails (`Agitate.Preresolved`). `false`
  (`--ignore-preresolved`) restores upstream behaviour (`agitate` addition, DESIGN.md).
  -/
  preresolvedNeeds : Bool := true
  /--
  `modulate`: compute, for each selected non-module file, the module-system imports it would need as
  a `module` with `@[expose] public section` (or `public meta section`, see `metaGlobs`), and with
  `--fix` convert it (`agitate` addition, DESIGN.md "Converting non-module files: `modulate`").
  -/
  toModule : Bool := false
  /-- `modulate --meta <GLOB>`: files to convert with `public meta section`. -/
  metaGlobs : Array Lake.Glob := #[]
  keepImplied : Bool := false
  keepPrefix : Bool := false
  keepPublic : Bool := false
  addPublic : Bool := false
  force : Bool := false
  githubStyle : Bool := false
  explain : Bool := false
  trace : Bool := false
  fix : Bool := false
  /-- `<MODULE>..`: the list of root modules to check -/
  mods : Array Name := #[]
  /-- The list of modules to minimize exclusively, otherwise all reachable ones. -/
  onlyMods : Array Name := #[]

/-- Which tool is running; decides which options exist. -/
inductive Tool where
  /-- `agitate`: code using the module system (`lake shake` semantics). -/
  | module
  /-- `agitate-nonmodule`: code not using the module system. -/
  | nonModule
  /-- `modulate`: converting code to the module system. -/
  | modulate
deriving BEq

def Tool.exeName : Tool → String
  | .module => "agitate"
  | .nonModule => "agitate-nonmodule"
  | .modulate => "modulate"

def usage (tool : Tool) : String :=
  let header := match tool with
    | .module => "agitate: a Lean import minimizer for code using the module system
(an olean-based reimplementation of `lake shake`)"
    | .nonModule => "agitate-nonmodule: a Lean import minimizer for code not using the module system"
    | .modulate => "modulate: converts non-module files to the module system (`modulize` + `agitate`).
For each selected non-module file, computes the imports it needs as a `module` with
`@[expose] public section` (or `public meta section`), from its oleans; with `--fix`, converts it"
  let moduleOnly := if tool == .nonModule then "" else if tool == .modulate then "
  --meta <GLOB>    convert the matching files with `public meta section` instead of
                   `@[expose] public section` (repeatable; Lake globs: `Foo`, `Foo.*` for `Foo` and
                   its submodules, `Foo.+` for its submodules only)" else "
  --keep-public    preserve all `public` imports
  --add-public     add new imports as `public` where they were previously reachable publicly
  --upstream-indirect
                   count an indirect module use only if the module reaches the recording module
                   through an import of exactly the same kind, as `lake shake` does
  --compat         behave exactly like `lake shake`: `--upstream-reserved --ignore-reserved-refs
                   --upstream-indirect --ignore-implemented-by --upstream-duplicates
                   --ignore-preresolved` and no ignored indirect kinds (later options override)"
  s!"{header}

USAGE:
  {tool.exeName} [OPTIONS] [MODULE...]

Run in the workspace's root directory. Modules are resolved through the Lake workspace (its
packages, root first, then the toolchain), never through LEAN_PATH; without MODULEs, the root
package's default targets are checked.

OPTIONS:
  --keep-implied   keep imports implied by other imports
  --keep-prefix    prefer importing a parent module that re-exports the needed one
  --gh-style       also print GitHub-style warnings
  --explain        explain why each kept or added import is needed
  --trace          trace the decision procedure
  --fix            apply the suggested edits to source files
  --only <MODULE>  minimize only this module (repeatable)
  --profile        print per-phase timings to stderr{moduleOnly}
  --upstream-reserved
                   compute reserved names exactly as `lake shake` does, including the quirks
                   agitate fixes (see DESIGN.md, \"Reserved names\")
  --ignore-reserved-refs
                   drop references to reserved names, as `lake shake` does, instead of counting
                   them as references to the declaration they are regenerated from
  --ignore-implemented-by
                   do not count the target of `@[implemented_by g] def f` as needed by `f`'s module,
                   as `lake shake` does (its `--fix` result may then not build)
  --upstream-duplicates
                   charge every use of a name declared in several modules to the first declarer,
                   as `lake shake` does, instead of the module itself or the copy it saw
  --ignore-preresolved
                   do not count names that syntax quotations preresolved (`` `(foo) ``) as needed,
                   as `lake shake` does (expanding the quotation may then fail)
  --ignore-indirect-kind <KIND>
                   ignore indirect module uses recorded by attribute KIND (repeatable; `*` for all)
  --list-indirect-kinds
                   print the kinds of indirect module uses in the import closure, then exit
"

/-- Parses the command line of `tool`. -/
partial def parseArgs (tool : Tool) (args : Args) : List String → Except String Args
  | [] => .ok args
  | "--keep-implied" :: rest => parseArgs tool { args with keepImplied := true } rest
  | "--keep-prefix" :: rest => parseArgs tool { args with keepPrefix := true } rest
  | "--gh-style" :: rest => parseArgs tool { args with githubStyle := true } rest
  | "--explain" :: rest => parseArgs tool { args with explain := true } rest
  | "--trace" :: rest => parseArgs tool { args with trace := true } rest
  | "--fix" :: rest => parseArgs tool { args with fix := true } rest
  | "--force" :: rest => parseArgs tool { args with force := true } rest
  | "--profile" :: rest => parseArgs tool { args with profile := true } rest
  | "--list-indirect-kinds" :: rest => parseArgs tool { args with listIndirectKinds := true } rest
  | "--upstream-reserved" :: rest => parseArgs tool { args with upstreamReserved := true } rest
  | "--ignore-reserved-refs" :: rest => parseArgs tool { args with reservedRefsToBase := false } rest
  | "--ignore-implemented-by" :: rest => parseArgs tool { args with implementedByNeeds := false } rest
  | "--upstream-duplicates" :: rest => parseArgs tool { args with resolveDuplicates := false } rest
  | "--ignore-preresolved" :: rest => parseArgs tool { args with preresolvedNeeds := false } rest
  | ["--ignore-indirect-kind"] => .error "missing argument to `--ignore-indirect-kind`"
  | "--ignore-indirect-kind" :: kind :: rest =>
    parseArgs tool { args with ignoreIndirectKinds := args.ignoreIndirectKinds.push kind } rest
  | ["--meta"] => .error "missing argument to `--meta`"
  | "--meta" :: glob :: rest =>
    if tool != .modulate then .error "unknown option `--meta`" else
    match Lake.Glob.ofString? glob with
    | some g => parseArgs tool { args with metaGlobs := args.metaGlobs.push g } rest
    | none => .error s!"invalid glob `{glob}`"
  | ["--only"] => .error "missing argument to `--only`"
  | "--only" :: mod :: rest =>
    parseArgs tool { args with onlyMods := args.onlyMods.push mod.toName } rest
  | arg :: rest =>
    match tool, arg with
    | .module, "--keep-public" => parseArgs tool { args with keepPublic := true } rest
    | .module, "--add-public" => parseArgs tool { args with addPublic := true } rest
    | .module, "--upstream-indirect" => parseArgs tool { args with indirectViaPublic := false } rest
    | .module, "--compat" =>
      parseArgs tool { args with upstreamReserved := true, reservedRefsToBase := false,
                                 ignoreIndirectKinds := #[], indirectViaPublic := false,
                                 implementedByNeeds := false, resolveDuplicates := false,
                                 preresolvedNeeds := false } rest
    | _, _ =>
      if arg.startsWith "-" then .error s!"unknown option `{arg}`"
      else parseArgs tool { args with mods := args.mods.push arg.toName } rest

/-- Runs `act`, printing its wall-clock time to stderr under `--profile`. -/
def Args.timed {α} (args : Args) (phase : String) (act : IO α) : IO α := do
  if !args.profile then act else
  let t0 ← IO.monoNanosNow
  let a ← act
  let t1 ← IO.monoNanosNow
  IO.eprintln s!"[profile] {phase}: {(t1 - t0) / 1000000} ms"
  return a

/--
The `main` of both tools: parses `argv`, loads the Lake workspace in the working directory, and runs
`run`. Modules are resolved through the workspace (`Resolver`), never through `LEAN_PATH` or
`LEAN_SRC_PATH`. Without modules on the command line, the root package's default target roots are
checked, as `lake shake` does.
-/
def cliMain (tool : Tool) (run : Args → Resolver → IO UInt32) (argv : List String) : IO UInt32 := do
  if argv.contains "--help" || argv.contains "-h" then
    IO.println (usage tool)
    return 0
  let args ← match parseArgs tool {} argv with
    | .ok args => pure args
    | .error e => IO.eprintln s!"error: {e}\n\n{usage tool}"; return 2
  let args := if tool == .modulate then { args with toModule := true } else args
  let r ← args.timed "loading the Lake workspace" Resolver.load
  let args := if args.mods.isEmpty then { args with mods := r.defaultRoots } else args
  if args.mods.isEmpty then
    IO.eprintln s!"error: no modules specified and there are no applicable default targets\n\n{usage tool}"
    return 2
  run args r

end Agitate
