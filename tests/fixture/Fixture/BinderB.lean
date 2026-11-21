/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

-- `binderThm` with `ε` explicit; see `Fixture.BinderA`.
public theorem binderThm (ε : Nat) (h : ε = ε) : ε = ε := h
