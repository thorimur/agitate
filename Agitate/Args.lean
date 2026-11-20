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
deriving BEq

def Tool.exeName : Tool → String
  | .module => "agitate"
  | .nonModule => "agitate-nonmodule"

def usage (tool : Tool) : String :=
  let header := match tool with
    | .module => "agitate: a Lean import minimizer for code using the module system
(an olean-based reimplementation of `lake shake`)"
    | .nonModule => "agitate-nonmodule: a Lean import minimizer for code not using the module system"
  let moduleOnly := if tool == .nonModule then "" else "
  --keep-public    preserve all `public` imports
  --add-public     add new imports as `public` where they were previously reachable publicly
  --upstream-indirect
                   count an indirect module use only if the module reaches the recording module
                   through an import of exactly the same kind, as `lake shake` does
  --compat         behave exactly like `lake shake`: `--upstream-reserved --ignore-reserved-refs
                   --upstream-indirect --ignore-implemented-by` and no ignored indirect kinds
                   (later options override)"
  s!"{header}

USAGE:
  lake env {tool.exeName} [OPTIONS] <MODULE>...

Run through `lake env` (or `lake exe`) so that LEAN_PATH and LEAN_SRC_PATH point at the
workspace.

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
  | ["--ignore-indirect-kind"] => .error "missing argument to `--ignore-indirect-kind`"
  | "--ignore-indirect-kind" :: kind :: rest =>
    parseArgs tool { args with ignoreIndirectKinds := args.ignoreIndirectKinds.push kind } rest
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
                                 implementedByNeeds := false } rest
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
The `main` of both tools: parses `argv` and runs `run` with the same search paths as `lake shake`
(`LEAN_PATH` via `initSearchPath`, and `LEAN_SRC_PATH`).
-/
def cliMain (tool : Tool) (run : Args → SearchPath → IO UInt32) (argv : List String) : IO UInt32 := do
  if argv.contains "--help" || argv.contains "-h" then
    IO.println (usage tool)
    return 0
  let args ← match parseArgs tool {} argv with
    | .ok args => pure args
    | .error e => IO.eprintln s!"error: {e}\n\n{usage tool}"; return 2
  if args.mods.isEmpty then
    -- TODO: default to the workspace's default target roots, as `lake shake` does.
    IO.eprintln s!"error: no modules specified\n\n{usage tool}"
    return 2
  initSearchPath (← findSysroot)
  let srcSearchPath := (← IO.getEnv "LEAN_SRC_PATH").map System.SearchPath.parse |>.getD []
  run args srcSearchPath

end Agitate
