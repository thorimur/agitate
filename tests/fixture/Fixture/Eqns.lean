/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
module

@[expose] public def f : Nat → Nat
  | 0 => 1
  | n + 1 => f n + 1
