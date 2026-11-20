/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
-- Instance resolution finds `natWidget` only through `Fixture.InstAttr` and records nothing:
-- only the indirect use (kind `instance`) keeps this import.
import Fixture.InstAttr

def instUse : Widget := HasWidget.w (α := Nat)
