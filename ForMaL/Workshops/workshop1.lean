/- # Basics: rewriting, calculating, reasoning forwards and backwards
References: [MIL] Mathematics in Lean, [Tut] Tutorials project.
Most of the demonstration section comes [MIL].
-/

import Mathlib.Tactic

/-
# Rewriting and calculating
-/

-- Lean knows some lemmas about real numbers.
#check mul_comm
#check mul_assoc

-- The rewrite tactic `rw` can use these lemmas.
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc] -- no need to supply variables here

-- Can also rewrite backwards by adding `<-` within `rw`, and use hypotheses.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

-- A `calc` block can help to structure a sequence of rewrites.
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

/-
# Forwards reasoning
-/

-- Can proceed from the hypotheses to the goal. E.g. can rewrite in hypotheses.
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp -- Having constructed the exact goal in the context, we use exact.

-- The `have` tactic allows for the introduction of intermediate hypotheses.
theorem mul_zero (a : ℝ) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

/-
#  Backwards reasoning
-/

-- Work on the goal. If the conclusion of therem_X is the same as the goal, then apply theorem_X and the new goal will be the hypotheses of theorem_X.
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  . apply h₁

/-
# And finally....
-/

-- Lean has some powerful tactics for working in rings and solving linear inequalities.

example (a b : ℝ) : a + b + a = 2 * a + b := by
  ring

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith

/-
# Exercises
-/

-- 1. Prove this using rw [MIL 2.1]
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry

-- 2. Prove this using rw [MIL 2.1]
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  sorry

-- 3. Prove this using calc [MIL 2.1]
example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry

-- 4. Prove this using forwards reasoning.  You may need `sub_self` [Tut 0004]
#check sub_self
example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry

-- 5. Prove this using forwards reasoning, using have. You may need `sub_nonneg` [Tut 0009]
#check sub_nonneg
example (a b : ℝ) (hab : a ≤ b) (c : ℝ) : a + c ≤ b + c := by
  sorry

-- 6. Here are some lemmas about the ≤ relation. You may find them useful to prove the following using backwards reasoning with apply. [MIL 2.3]

#check lt_of_le_of_lt
#check lt_of_lt_of_le
#check lt_trans

example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  sorry
