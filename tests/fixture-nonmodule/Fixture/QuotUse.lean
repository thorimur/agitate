/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
-- Expands the quotation of `Fixture/QuotMacro.lean`. Fails to build (`Unknown identifier`) after
-- `--fix` with `--ignore-preresolved`.
import Fixture.QuotMacro

def quotUse : Nat := quot_target
