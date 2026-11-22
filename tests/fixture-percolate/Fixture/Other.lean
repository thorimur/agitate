/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
-- Not imported by the seeds' modules: everything here is unused.
module

public import Fixture.Base

@[expose] public section

def other : Nat := Point.sum ⟨1, 1⟩
