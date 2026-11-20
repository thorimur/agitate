/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
-- Refers to the reserved name `f.eq_1`, realized in `Fixture.EqnRealize`; it counts as a
-- reference to `f`, so `Fixture.EqnRealize` can be replaced by `Fixture.Eqns`.
import Fixture.EqnRealize

theorem f_zero : f 0 = 1 := f.eq_1
