/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
-- `@[implemented_by gImpl]` names `gImpl` only in an attribute argument; nothing records it, but
-- this declaration and compiled callers of `ibF` need it, so the import must stay.
import Fixture.IbImpl

@[implemented_by gImpl] def ibF (n : Nat) : Nat := n + 1
