module

public import Fixture.Eqns

-- Realizes the equation lemmas of `f` in this module.
public theorem f_one : f 1 = 2 := by simp [f]
