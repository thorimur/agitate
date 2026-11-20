/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import Fixture.Eqns

-- Realizes the equation lemmas of `f` in this module.
theorem f_one : f 1 = 2 := by simp [f]
