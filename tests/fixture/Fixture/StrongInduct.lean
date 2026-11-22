/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

public def Reach (n : Nat) : Prop := n = 0 ∨ Reach (n + 1)
  inductive_fixpoint

-- Realizes the reserved name `Reach.strong_induct` (reserved since Lean `v4.36.0`). Checked by
-- `agitate-check`.
public theorem Reach.strong (pred : Nat → Prop)
    (hyp : ∀ n, n = 0 ∨ pred (n + 1) ∧ Reach (n + 1) → pred n) (n : Nat) : Reach n → pred n :=
  Reach.strong_induct pred hyp n
