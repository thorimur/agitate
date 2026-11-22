/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

-- `bv_decide` checks that `Std.Tactic.BVDecide` itself is loaded (`ensureBvDecide`), which leaves
-- no trace in the oleans.
public import Std.Tactic.BVDecide -- shake: keep

public inductive Color where
  | red | green | blue

-- Realizes `bv_decide`'s reserved enum names for `Color` (`Color.enumToBitVec`, …), which since
-- Lean `v4.36.0` are private to the realizing module. Checked by `agitate-check`.
public theorem Color.red_ne_green (c : Color) (h : c = .red) : c ≠ .green := by
  bv_decide
