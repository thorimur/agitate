/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
-- `simp` finds `a_eq` only through `Fixture.SimpAttr`, and records that itself.
import Fixture.SimpAttr

theorem simpUse : a + 0 = 1 := by simp
