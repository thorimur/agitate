/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
structure Widget where
  n : Nat

class HasWidget (α : Type) where
  w : Widget

/-- An instance-shaped definition that is not an instance here. -/
@[instance_reducible] def natWidget : HasWidget Nat := ⟨⟨3⟩⟩
