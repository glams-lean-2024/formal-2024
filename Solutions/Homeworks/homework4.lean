/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Library

/-!
# Homework 4: Functions
References: [MIL] Mathematics in Lean, [Tut] Tutorials project.
Most of this homework is taken from [MIL 4.2]
-/

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function

-- If `f : α → β` is a function and `p` is a set of elements of type `β`,
-- the library defines `preimage f p`, written `f ⁻¹' p`, to be `{ x | f x ∈ p }`.


example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext x -- The expression `x ∈ f ⁻¹' p` reduces to `f x ∈ p`
  rfl

-- If `s` is a set of elements of type `α`, the library also defines `image f s`, written `f '' s`,
-- to be `{ y | ∃ x, x ∈ s ∧ f x = y }`. So a hypothesis `y ∈ f '' s` decomposes to a triple
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
  constructor
  . intro h x xs
    exact h ⟨x, xs, rfl⟩
  . rintro h x ⟨y, ys, rfl⟩
    exact h ys

-- 2
example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, ⟨hy, hxy⟩⟩
  rw [← h hxy]
  exact hy

-- 3
example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, h, rfl⟩
  exact h

-- 4
example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro x ⟨h₁, h₂⟩
  exact ⟨h₁, h₂⟩

-- 5
example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y; constructor
  · rintro ⟨⟨x, ⟨hxs, rfl⟩⟩, hxy⟩
    use x, ⟨hxs, hxy⟩
  . rintro ⟨x, ⟨xs, h⟩, rfl⟩
    use ?_, h
    use x, xs

-- 6
example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨hx, hx2⟩
  use ?_, hx2
  use x, hx

-- 7
example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (h | h)
  · left
    use x, h
  . right
    exact h


end


section

-- Let us consider functions `ℝ → ℝ`

open Set Real

-- `InjOn f s` is a predicate that means the function `f` is injective on `s`

#print InjOn

def PosReals : Set ℝ := { x : ℝ | 0 < x }

example : InjOn log PosReals := by
  intro x xpos y ypos
  intro e
  -- `log x = log y`
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]

-- `range f` is defined as the set `{ x : ℝ | ∃ y : ℝ, f y = x }`

#print range

example : range exp = PosReals := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

-- You may need the following theorems:

#check sqrt_nonneg
#check pow_nonneg

def NonNegReals : Set ℝ := { x : ℝ | 0 ≤ x }

-- 8
example : InjOn sqrt NonNegReals := by
  intro x xpos y ypos hxy
  rw [← sq_sqrt xpos, hxy, sq_sqrt ypos]

-- 9
example : InjOn (fun x ↦ x ^ 2) NonNegReals := by
  intro x xpos y ypos hxy
  dsimp at *
  rw [← sqrt_sq xpos, hxy, sqrt_sq ypos]

-- 10
example : sqrt '' NonNegReals = NonNegReals := by
  ext y; constructor
  · rintro ⟨x, _, rfl⟩
    exact sqrt_nonneg _
  intro ypos
  use y ^ 2
  rw [sqrt_sq ypos]
  exact ⟨sq_nonneg y, rfl⟩

-- 11
example : (range fun x ↦ x ^ 2) = NonNegReals := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    exact sq_nonneg x
  intro ypos
  use sqrt y
  simp_rw [sq_sqrt ypos]

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
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by
    rw [← h] at h₂
    contradiction
  contradiction

end
