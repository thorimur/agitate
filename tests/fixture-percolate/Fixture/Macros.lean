/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
-- A public metaprogram reaching runtime code through a private meta helper: the helper's code
-- must be presentable, so `Fixture.Runtime` must stay a *public* meta import.
module

public meta import Fixture.Runtime

public section

private meta def tripleHelper (n : Nat) : Nat := triple n

meta def tripleTwo : Nat := tripleHelper 2

macro "six" : term => return Lean.Syntax.mkNumLit (toString tripleTwo)
