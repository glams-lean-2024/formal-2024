/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Library

/-!
# Homework 1: Basics
References: [MIL] Mathematics in Lean, [Tut] Tutorials project.
-/


/-
# Problem  1
Please read the following and complete the exercises below. This is a section from [Tut]. The exercise is to prove the same statement using backwards reasoning, forwards reasoning, and a combination of both.
-/

/-
We are going to prove that multiplication by a nonnegative real number preserves the ≤ relation on real numbers. That is: for real numbers `a, b, c`, if `a ≤ b` and `0 ≤ c`, then `a * c ≤ b * c`. We will use the following lemmas:
-/

#check sub_nonneg
#check mul_nonneg

/-
We first prove this using backwards reasoning: using `apply` to announce the use of a lemma, and provide proofs after the fact, and using `rw` on the goal.
-/

example (a b c : ℝ) (hc : 0 ≤ c) (hab : a ≤ b) : a * c ≤ b * c := by
  rw [← sub_nonneg]
  have key : b * c - a * c = (b - a) * c := by ring
  rw [key]
  apply mul_nonneg
  -- Here we don't provide proofs for the lemma's assumptions
  -- Now we need to provide the proofs.
  -- There are now two things to prove. We use the center dot (typed using `\.`) to
  -- focus on the current first goal.
  · rw [sub_nonneg]
    exact hab
  · exact hc

/-
Let's prove the same statement using only forward reasoning: announcing stuff,
proving it by working with known facts, moving forward.
-/
example (a b c : ℝ) (hc : 0 ≤ c) (hab : a ≤ b) : a * c ≤ b * c := by
  have hab' : 0 ≤ b - a := by
    rw [← sub_nonneg] at hab
    exact hab
  have h₁ : 0 ≤ (b - a) * c := mul_nonneg hab' hc
  have h₂ : (b - a) * c = b * c - a * c := by ring
  have h₃ : 0 ≤ b * c - a * c := by
    rw [h₂] at h₁
    exact h₁
  rw [sub_nonneg] at h₃
  exact h₃

/-
One reason why the backward reasoning proof is shorter is because Lean can
infer of lot of things by comparing the goal and the lemma statement. Indeed
in the `apply mul_nonneg` line, we didn't need to tell Lean that `x = b - a`
and `y = c` in the lemma. It was infered by "unification" between the lemma
statement and the goal.

To be fair to the forward reasoning version, we should introduce a convenient
variation on `rw`. The `rwa` tactic performs rewrite and then looks for an
assumption matching the goal. We can use it to rewrite our latest proof as:
-/
example (a b c : ℝ) (hc : 0 ≤ c) (hab : a ≤ b) : a * c ≤ b * c := by
  have hab' : 0 ≤ b - a := by rwa [← sub_nonneg] at hab
  have h₁ : 0 ≤ (b - a) * c := mul_nonneg hab' hc
  have h₂ : (b - a) * c = b * c - a * c := by ring
  have h₃ : 0 ≤ b * c - a * c := by rwa [h₂] at h₁
  rwa [sub_nonneg] at h₃

/-
Let's now combine forward and backward reasoning, to get our most
efficient proof of this statement. Note in particular how unification is used
to know what to prove inside the parentheses in the `mul_nonneg` arguments.
-/
example (a b c : ℝ) (hc : 0 ≤ c) (hab : a ≤ b) : a * c ≤ b * c := by
  rw [← sub_nonneg]
  calc
    0 ≤ (b - a) * c := mul_nonneg (by rwa [sub_nonneg]) hc
    _ = b * c - a * c := by ring


/-
Let's now practice all three styles using the following lemmas to help:
-/

#check mul_nonneg_of_nonpos_of_nonpos
#check sub_nonpos

-- First using mostly backward reasoning
-- 0013
example (a b c : ℝ) (hc : c ≤ 0) (hab : a ≤ b) : b * c ≤ a * c := by
  sorry

-- Using forward reasoning
-- 0014
example (a b c : ℝ) (hc : c ≤ 0) (hab : a ≤ b) : b * c ≤ a * c := by
  sorry

-- 0015
/-- Using a combination of both, with a `calc` block -/
example (a b c : ℝ) (hc : c ≤ 0) (hab : a ≤ b) : b * c ≤ a * c := by
  sorry
