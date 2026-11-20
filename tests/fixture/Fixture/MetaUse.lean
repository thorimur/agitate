module

public meta import Fixture.MetaDef
public meta import Fixture.B
public import Fixture.A

-- `Fixture.MetaDef` is needed at compile time only; `Fixture.B` is not needed at all.
meta def useMeta : Nat := metaVal + 1
public def metaUse : Nat := a
