/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

-- `simp` finds `a_eq` only through `Fixture.SimpAttr`. `simp` records an extra module use for the
-- attribute's module itself, so this import stays even with the `simp` indirect uses ignored.
public import Fixture.SimpAttr

public theorem simpUse : a + 0 = 1 := by simp
