/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
-- Used by `Fixture.Use` only through notation: an extra module use naming no declaration, so every
-- item here is unattributed.
module

public import Fixture.Base

@[expose] public section

notation "⟪" a ", " b "⟫" => Point.mk a b

def notationFileDef : Nat := 1

attribute [simp] Point.sum
