/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

-- Uses `Fixture.Pre.Impl` through `Fixture.Pre`; `--keep-prefix` keeps the parent module.
public import Fixture.Pre

public def prefixUse : Nat := impl
