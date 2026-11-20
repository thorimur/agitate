/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

-- Folder-nested imports are preserved even when unused.
public import Fixture.Nested.Sub
public import Fixture.A

public def nested : Nat := a
