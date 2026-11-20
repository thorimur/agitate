module

public import Fixture.IbDecl

-- A compiled call of `ibF` from another module.
public def ibUse : IO Unit := IO.println (ibF 1)
