/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

-- Expands quotations of `Fixture/QuotMacro.lean` and `Fixture/QuotHelper.lean`. Fails to build
-- (`Unknown identifier`) after `--fix` with `--ignore-preresolved` or `--compat`.
public import Fixture.QuotMacro
public import Fixture.QuotHelper

public def quotUse : Nat := quot_target + quot_helper
