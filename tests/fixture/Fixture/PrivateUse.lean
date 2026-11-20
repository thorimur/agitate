module

-- `a` is only used in a non-exposed body, so a private import suffices.
public import Fixture.A

public def privateUse : Nat := a
