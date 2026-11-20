/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

public import Fixture.A

-- An attribute on an imported declaration records an indirect module use of kind `simp`.
attribute [simp] a_eq
