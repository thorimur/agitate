/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
-- Declares `dupThm` too (identical, so imports can merge it with `Fixture.DupA`'s) and uses its
-- own. `Fixture.DupA` comes first in import order: upstream would charge the use to it.
theorem dupThm : 1 + 1 = 2 := rfl

theorem dupUseB : 1 + 1 = 2 := dupThm
