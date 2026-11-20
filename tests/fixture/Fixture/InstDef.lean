module

public structure Widget where
  n : Nat

public class HasWidget (α : Type) where
  w : Widget

/-- An instance-shaped definition that is not an instance here. -/
@[expose, instance_reducible] public def natWidget : HasWidget Nat := ⟨⟨3⟩⟩
