/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

public meta import Fixture.MetaDef
public meta import Fixture.B
public import Fixture.A

-- `Fixture.MetaDef` is needed at compile time only; `Fixture.B` is not needed at all.
meta def useMeta : Nat := metaVal + 1
public def metaUse : Nat := a
