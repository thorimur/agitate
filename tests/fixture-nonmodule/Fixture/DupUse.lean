/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
-- Reaches `dupThm` only through `Fixture.DupB`, which must stay.
import Fixture.DupB

theorem dupUse : 1 + 1 = 2 := dupThm
