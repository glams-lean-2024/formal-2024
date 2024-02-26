/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Library

/-!
  # Homework 5: More on types
  References: [MIL] Mathematics in Lean, [Tut] Tutorials project.
  This week we will also use the textbook [TPL] Theorem Proving in Lean 4, which can
  be found at https://leanprover.github.io/theorem_proving_in_lean4/
-/

/-
  ## Q1: Unique existence
  Before we move on to working with types, we will introduce the useful `∃!` notation.
  Given a type `α` and `p : α → Prop`, `∃! x : α, p x` is a proposition asserting that there
  exists a unique term `x : α` such that `p x` holds.
-/

-- Examine the following example to see how `∃!` is defined; then try to prove it.
example : ∃! x : ℕ, x = 0 := by
  dsimp [ExistsUnique]
  sorry

-- The `∃!` can take several variables, but this can be quite confusing.
-- For example, try to understand what the following lemma is saying, and then prove it.
lemma Nat.exists_unique_le : ∃! n m : Nat, m ≤ n := by
  sorry


/-
  ## Q2: Types and logic
  Here we examine some interesting interactions between types and logic.
-/

-- Lean has an inductive type (class) called `Nonempty`. It represents when a type has at least
-- one term. You can `Ctrl+Click` on `Nonempty` to see its definition.
#check Nonempty

-- Given that it is an inductive type, do you see how you could use and construct a term of
-- type `Nonempty α` for some type `α`? Try the following:

example : Nonempty ℕ := sorry

example {α β : Type} : Nonempty α → Nonempty β → Nonempty (α × β) := sorry

-- Now try to understand and prove the following lemma.
lemma existence_implies_everything_iff {α : Type*} (r : α → Prop) :
  (∃ x, (r x → ∀ y, r y)) ↔ Nonempty α := sorry

/-
  ## Q3: Type equality

-/
