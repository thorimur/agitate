/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
-- `Fixture.A` is implied by `Fixture.B` (imports re-export), so it is removed
-- unless `--keep-implied`.
import Fixture.A
import Fixture.B

def implied : Nat := a + b
