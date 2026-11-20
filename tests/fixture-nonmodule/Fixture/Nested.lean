/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
-- Folder-nested imports are preserved even when unused.
import Fixture.Nested.Sub
import Fixture.A

def nested : Nat := a
