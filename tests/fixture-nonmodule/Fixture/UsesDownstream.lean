/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
-- `Fixture.Downstream` is unused here but marked `shake: keep-downstream`.
import Fixture.Downstream
import Fixture.B

def usesDownstream : Nat := b
