/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

-- Declares `dupThm` too (identical, so imports can merge it with `Fixture.DupA`'s) and uses its
-- own. `Fixture.DupA` comes first in import order: upstream charges the use to it and adds it.
public theorem dupThm : 1 + 1 = 2 := rfl

public theorem dupUseB : 1 + 1 = 2 := dupThm
