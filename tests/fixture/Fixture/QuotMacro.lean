/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

-- The quotation preresolves `quotTarget`: the macro's term holds only the name, so nothing else
-- uses this import, and Lean records no extra use. Without it, the quotation finds nothing and
-- every expansion fails (`Fixture/QuotUse.lean`). The macro's declaration is exported, so the
-- import stays public (`Agitate.Preresolved`).
public import Fixture.QuotTarget

macro "quot_target" : term => `(quotTarget)
