import Fixture.IbDecl

-- A compiled call of `ibF` from another module.
def ibUse : IO Unit := IO.println (ibF 1)
