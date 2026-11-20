/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import Fixture.IbDecl

-- A compiled call of `ibF` from another module.
def ibUse : IO Unit := IO.println (ibF 1)
