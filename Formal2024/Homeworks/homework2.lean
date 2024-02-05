/-
# Homework 1: Logic
References: [MIL] Mathematics in Lean, [Tut] Tutorials project.
Most of this homework is taken from [Tut04]
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-
The next exercises use divisibility in ℤ (beware the ∣ symbol which is
not ASCII). This is done by writing `\|`.

By definition, a ∣ b ↔ ∃ k, b = a*k, so you can prove a ∣ b using the
`use` tactic.
-/
-- Until the end of this file, a, b and c will denote integers, unless
-- explicitly stated otherwise
variable (a b c : ℤ)

-- [TUT] 0029
example (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  sorry

/-
A very common pattern is to have an assumption or lemma asserting
  `h : ∃ x, y = ...`
and this is used through the combo:
  rcases h with ⟨x, hx⟩
  rw hx at ...
The tactic `rcases` allows us to simplify the above combo when the
name `hx` is replaced by the special name `rfl`, as in the following example.
-/
example (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b + c := by
  rcases h1 with ⟨k, rfl⟩
  rcases h2 with ⟨l, rfl⟩
  use k + l
  ring

-- Now it's your turn! Prove the following:


example : a ∣ b → a ∣ c → a ∣ b + c := by
/-
To get an even shorter proof, you can use the same `rfl` trick with
the `rintro` tactic too. Try proving it both ways.
-/
  sorry

open Function

-- In the remaining of this file, f and g will denote functions from ℝ to ℝ.
variable (f g : ℝ → ℝ)

-- [TUT] 0031
example (h : Surjective (g ∘ f)) : Surjective g := by
  sorry
/-
The above exercise can be done in three lines. Try to do the next exercise in four lines.
-/
-- [TUT] 0032
example (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  sorry


-- Of the following 4 exercises, 3 can be done with elementary logic, one needs contradiction.
-- Some are trivial after applying `push_neg`. Try doing them explicitly too, as an exercise.
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  sorry

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  sorry

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  sorry
