/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/

/-
# Homework 4: Functions
References: [MIL] Mathematics in Lean, [Tut] Tutorials project.
Most of this homework is taken from [MIL 4.2]
-/

import Library

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function

-- If `f : α → β` is a function and `p` is a set of elements of type `β`,
-- the library defines `preimage f p`, written `f ⁻¹' p`, to be `{x | f x ∈ p}`.


example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext x -- The expression `x ∈ f ⁻¹' p` reduces to `f x ∈ p`
  rfl

-- If `s` is a set of elements of type `α`, the library also defines `image f s`, written `f '' s`,
-- to be `{y | ∃ x, x ∈ s ∧ f x = y}`. So a hypothesis `y ∈ f '' s` decomposes to a triple
-- `⟨x, xs, xeq⟩` with `x : α` satisfying the hypotheses `xs : x ∈ s` and `xeq : f x = y`.
-- The `rfl` tag in the `rintro` tactic was made precisely for this sort of situation.

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩ -- Notice how `rfl` automatically rewrites `f x = y`
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt


example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  -- The goal decomposes to
  use x, xs


-- 1
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  sorry

-- 2
example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  sorry

-- 3
example : f '' (f ⁻¹' u) ⊆ u := by
  sorry

-- 4
example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

-- 5
example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

-- 6
example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

-- 7
example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry


end


section

-- Let us consider functions `ℝ → ℝ`

open Set Real

-- `InjOn f s` is a predicate that means "`f` is injective on `s`"

#print InjOn

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]

-- We also define `range f` as `{x | ∃y, f y = x}`

#print range

example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

-- You may need the following theorems:

#check sqrt_nonneg
#check pow_nonneg


-- 8
example : InjOn sqrt { x | x ≥ 0 } := by
  sorry

-- 9
example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

-- 10
example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

-- 11
example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry

end


section
variable {α : Type*}
open Function

-- This is a type-theoretic statement of Cantor’s famous theorem that there is no surjective
-- function from a set to its power set. See if you can understand the proof,
-- and then fill in the two lines that are missing.

-- 12

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction


end
