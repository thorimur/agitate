/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

-- As `Fixture/QuotMacro.lean`, but the quotation is in a private helper of the macro. agitate
-- takes the helper's visibility and keeps only a private import, although the quotation runs
-- wherever the macro is used (a known limitation, DESIGN.md "Preresolved names in quotations").
-- The `--fix` result still builds: expansion sites refer to `quotHelperTarget` themselves and
-- import it directly.
public import Fixture.QuotHelperTarget

private meta def mkQuot : Lean.MacroM (Lean.TSyntax `term) := `(quotHelperTarget)

macro "quot_helper" : term => mkQuot
