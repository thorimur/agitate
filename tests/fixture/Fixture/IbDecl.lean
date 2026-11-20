module

-- `@[implemented_by gImpl]` names `gImpl` only in an attribute argument; nothing records it, but
-- compiled callers of `ibF` in other modules need it, so the import must stay (and stay public).
public import Fixture.IbImpl

@[implemented_by gImpl] public def ibF (n : Nat) : Nat := n + 1
