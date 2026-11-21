/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
-- Both copies of `binderThm` are imported; `Fixture.BinderB` loads last, so its copy (explicit `ε`)
-- is the one this module sees and relies on; keeping only `Fixture.BinderA` would break the call.
import Fixture.BinderA
import Fixture.BinderB

theorem binderUse : 1 = 1 := binderThm 1 rfl
