/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
-- Runtime code used by a public metaprogram in `Fixture.Macros`: that needs a public meta import.
module

@[expose] public section

def triple (n : Nat) : Nat := 3 * n

def unusedRuntime : Nat := 0
