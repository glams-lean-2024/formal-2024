/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Library

/-!
  # Logic: Conjunction, Iff, and Disjunction
  References: [MIL] Mathematics in Lean, [Tut] Tutorials project.
  Most of the demonstration section comes [MIL].
-/


/-!
  # Conjunction
-/

-- The symbol for conjunction is `∧`, which you can write as `\and`.

-- To prove a conjunction, we use the `constructor` tactic.
-- This will split the goal into two, one for each part of the conjunction.
-- (For people familiar with Lean 3: the `split` tactic is gone in Lean 4.)

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

-- Here is another example:
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption -- This tactic looks for a hypothesis in the context that matches the goal, like `h₀`.
  · intro h
    apply h₁
    rw [h]

-- You can also use the anonymous constructor `⟨⟩`:
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  exact ⟨h₀, h⟩


-- To use a conjunction, you can use `rcases` or `rintro`, as with existential quantifiers.
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h' -- Recall that `¬P` is defined as `P → False`.
  apply h₁
  exact le_antisymm h₀ h'

-- You can also access the parts of a conjunction `h` with `h.left` and `h.right` (or `h.1` and `h.2`).
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')

-- You can nest anonymous constructors, even if they mix conjunctions and existential quantifiers.
-- Note that they (usually) associate to the right.
example : ∃ x : ℕ, 3 < x ∧ x < 5 ∧ ∃ y, y^2 = x :=
  ⟨4, by norm_num, by norm_num, 2, by norm_num⟩


/-!
  # Iff
-/

-- The symbol for iff is `↔`, which you can write as `\iff`.

-- As with `∧`, you can use the `constructor` tactic, or the anonymous constructor `⟨⟩` to prove an iff.
-- Similarly, you can use an iff with `rcases` or `rintro`.
-- If `h` is an iff, you can access the two implications with `h.mp` and `h.mpr` (or `h.1` and `h.2`).

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · intro h' heq
    apply h'
    rw [heq]
  · intro h' hle
    apply h'
    exact le_antisymm h hle


-- Lean knows that `↔` is reflexive, symmetric, and transitive, so you can use the `rw` tactic with it.
#check abs_lt

example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith
-- The `<;>` tactic combinator attempts to close every goal opened by `constructor`
-- with the given tactic, in this case `linarith`.


/-!
  # Exercises
-/

-- 1. Try to prove this lemma in at least two different ways, e.g. using `constructor`, `⟨⟩`, `h.left` and `h.right`, etc. [MIL 3.4]

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  sorry


-- 2. Prove the following lemma. [MIL 3.4]

example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [Monotone] -- This unfolds the definition of `Monotone` in the goal.
  push_neg
  sorry


/-!
  # Disjunction
-/

-- The symbol for disjunction is `∨`, which you can write as `\or`.

-- To prove a disjunction, it is enough to prove one of the two sides.
-- You can use the `left` or `right` to choose which side you want to prove.

example {x y : ℝ} (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x] -- You can add extra hypotheses to `linarith` with square brackets.
  -- In this case we have added `x^2 ≥ 0`.

-- The proof term version of this is `Or.inl` and `Or.inr`.
example {x y : ℝ} (h : y > x ^ 2) : y > 0 ∨ y < -1 :=
  Or.inl (by linarith [pow_two_nonneg x])


-- To use a disjunction, you can use `rcases` or `rintro`, as with existential quantifiers and conjunctions.
-- The notation is slightly different: you use `|` instead of `⟨⟩`.
-- When we use a disjunction, we have to prove the goal for each side of the disjunction.
example {x y : ℝ} : x < |y| → x < y ∨ x < -y := by
  have ynegorpos : 0 ≤ y ∨ 0 > y := le_or_gt 0 y
  rcases ynegorpos with yneg | ypos
  · rw [abs_of_nonneg yneg]
    intro h; left; exact h -- The `;` allows us to write tactics on the same line.
  . rw [abs_of_neg ypos]
    intro h; right; exact h

-- You can nest patterns in `rcases` and `rintro`, even mixing `|` and `⟨⟩`.
-- Recall that the vertical bar symbol for divisibility is typed with `\|` but for disjunction or absolute value it is just `|`.
example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  -- Recall that using `rfl` in a pattern will rewrite the equation it replaces everywhere.
  -- Here the first `rfl` will replace `n` with `m * a`, and second will replace `k` with `m * b`.
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right


-- You can use this to split into cases, depending on whether a proposition is true or false.
-- To do this explicitly, you can use the law of the excluded middle:
#check em

example (P : Prop) : ¬¬P → P := by
  intro h
  rcases em P with hp | hnp
  · assumption
  . contradiction -- This tactic looks for a contradiction in the hypotheses, in this case `h` and `hnp`.

-- You can also do this using the `by_cases` tactic.
example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  -- `P` is the proposition we are splitting on, and `h'` is the name of the hypothesis we get.
  · assumption
  . contradiction


/-!
  # Exercises
-/

section
variable {x y : ℝ}

-- 3. Prove the triangle inequality. [MIL 3.5]

-- You may want to use the following lemmas:
#check le_abs_self x
#check neg_le_abs x

example (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  sorry


-- 4. Prove the following lemma. [MIL 3.5]

-- You may want to use the following lemma:
#check eq_zero_or_eq_zero_of_mul_eq_zero

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

end


-- 5. Prove the following equivalence, using `by_cases` in one direction [MIL 3.5]

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  sorry


-- 6. Here we define what it means for a function `ℝ → ℝ` to be nondecreasing.
-- Prove the following lemma [Tut 3]

def NonDecreasing (f : ℝ → ℝ) : Prop :=
  ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

-- You may want to use:
#check le_total

example (f : ℝ → ℝ) (h : NonDecreasing f) (h' : ∀ x, f (f x) = x) : ∀ x, f x = x := by
  sorry
