/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

-- Both copies of `binderThm` are imported; `Fixture.BinderB` loads last, so its copy (explicit `ε`)
-- is the one this module sees and relies on. `Fixture.BinderA` comes first in `ModuleIdx` order,
-- so charging the first declarer (upstream) keeps the wrong copy and the call fails to elaborate.
public import Fixture.BinderA
public import Fixture.BinderB

public theorem binderUse : 1 = 1 := binderThm 1 rfl
