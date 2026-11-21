/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

-- `binderThm` with `ε` implicit. `Fixture.BinderB` declares the same theorem with `ε` explicit;
-- imports merge the two (types are compared up to binder annotations).
public theorem binderThm {ε : Nat} (h : ε = ε) : ε = ε := h
