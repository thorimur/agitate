-- `@[implemented_by gImpl]` names `gImpl` only in an attribute argument; nothing records it, but
-- this declaration and compiled callers of `ibF` need it, so the import must stay.
import Fixture.IbImpl

@[implemented_by gImpl] def ibF (n : Nat) : Nat := n + 1
