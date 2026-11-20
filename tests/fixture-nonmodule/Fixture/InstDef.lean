structure Widget where
  n : Nat

class HasWidget (α : Type) where
  w : Widget

/-- An instance-shaped definition that is not an instance here. -/
@[instance_reducible] def natWidget : HasWidget Nat := ⟨⟨3⟩⟩
