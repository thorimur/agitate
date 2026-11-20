/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

-- `a` is only used in a non-exposed body, so a private import suffices.
public import Fixture.A

public def privateUse : Nat := a
