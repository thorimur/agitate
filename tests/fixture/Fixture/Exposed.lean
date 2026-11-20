/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

-- The exposed body needs `Fixture.A` publicly; `Fixture.B` is only used privately.
public import Fixture.A
public import Fixture.B

@[expose] public def exposed : Nat := a
public def notExposed : Nat := b
