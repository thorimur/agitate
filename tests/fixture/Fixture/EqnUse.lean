/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

-- Refers to the reserved name `f.eq_1`, realized in `Fixture.EqnRealize`.
public import Fixture.EqnRealize

public theorem f_zero : f 0 = 1 := f.eq_1
