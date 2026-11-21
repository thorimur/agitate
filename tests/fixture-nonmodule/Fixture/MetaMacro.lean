/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import Fixture.MetaHelper

syntax (name := helperStx) "helper%" : term

-- A metaprogram written as a plain `def` with an attribute: nothing records it as meta, so as a
-- module this file needs `public meta section` (`modulate --meta Fixture.MetaMacro`); with
-- `@[expose] public section` the attribute is rejected ("must be marked as `meta`").
@[macro helperStx] def helperImpl : Lean.Macro := fun _ =>
  return Lean.Syntax.mkNumLit (toString helperVal)
