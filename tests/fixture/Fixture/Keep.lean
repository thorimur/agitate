module

public import Fixture.A
public import Fixture.C -- shake: keep

public def keep : Nat := a
