/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
-- The seeds: `seed1` … `seed6` and `seedTree`.
module

public import Fixture.Base
public import Fixture.Notation

@[expose] public section

theorem seed1 : (⟪1, 2⟫ : Point).sum = 3 := rfl

theorem seed2 : double 2 = 4 := by simp [double]

def seedTree : Tree := leaf

def seed5 : Nat := withHelper 1

theorem seed6 (a b : Nat) : (Point.mk a b).sum = a + b := by dsimp only [Point.sum_mk]

def notSeed : Nat := Point.sum ⟨0, 0⟩

private def helper : Nat := 3

-- a private declaration used in a (non-exposed) proof
theorem seed3 : 3 = 3 := by
  have : helper = 3 := rfl
  rfl

-- macros used in their own module leave no record: meta items of a module with needed items are
-- unattributed
macro "three" : term => `(3)

theorem seed4 : (three : Nat) = 3 := rfl

macro "four" : term => `(4)
