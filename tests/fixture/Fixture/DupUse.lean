/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

-- Reaches `dupThm` only through `Fixture.DupB`; upstream replaces that import by `Fixture.DupA`,
-- which is not in this module's imports at all.
public import Fixture.DupB

public theorem dupUse : 1 + 1 = 2 := dupThm
