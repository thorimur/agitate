/-
Copyright (c) 2026 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
-- Declarations that `Fixture.Use`'s seeds need, or not.
module

@[expose] public section

/-- Fields, constructor and derived instance share the structure's item. -/
structure Point where
  x : Nat
  y : Nat
deriving Repr

def Point.sum (p : Point) : Nat := p.x + p.y

/-- An rfl lemma that `dsimp` uses without leaving a proof term (a candidate). -/
@[simp] theorem Point.sum_mk (a b : Nat) : (Point.mk a b).sum = a + b := rfl

def unusedDef : Nat := 42

theorem unusedThm : unusedDef ≤ 42 := Nat.le_refl _

/-- Its equation lemmas are realised in `Fixture.Use`; they belong to this item. -/
def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

-- mutual inductives: two items that need each other (a cycle)
mutual
inductive Tree where
  | node : Forest → Tree
inductive Forest where
  | nil : Forest
  | cons : Tree → Forest → Forest
end

def leaf : Tree := .node .nil

/-- A `where` helper is part of its declaration's item. -/
def withHelper (n : Nat) : Nat := go n
where go (k : Nat) : Nat := k + 1

def unusedWithHelper : Nat := go
where go : Nat := 0

/-- `simp` with a `↔` lemma creates a private auxiliary lemma `_simp_1` here. -/
theorem auxSimp (a b : Nat) (h : a ≤ b) : ¬ b < a := by simp [Nat.not_lt, h]
