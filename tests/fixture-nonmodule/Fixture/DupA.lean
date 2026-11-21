/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
-- Declares `dupThm`; so does `Fixture.DupB`, which does not import this module.
theorem dupThm : 1 + 1 = 2 := rfl
