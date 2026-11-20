/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

-- `@[implemented_by gImpl]` names `gImpl` only in an attribute argument; nothing records it, but
-- compiled callers of `ibF` in other modules need it, so the import must stay (and stay public).
public import Fixture.IbImpl

@[implemented_by gImpl] public def ibF (n : Nat) : Nat := n + 1
