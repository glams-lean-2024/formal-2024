/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Mathlib.Data.Real.Basic
import Library

/-!
# Homework 3: Sequences and convergence
References: [MIL] Mathematics in Lean, [Tut] Tutorials project.
Most of this homework is taken from [MIL 3.6]
-/

/-!
  In this homework you will be proving some basic facts about convergence of sequences of real numbers.
  You will meet some useful tactics along the way!

  For us, as sequence will be same thing as a function `s : ℕ → ℝ`.
-/

-- First, we define what it means for a sequence to converge to a fixed number.
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

-- The notation `∀ ε > 0, ...` is shorthand for `∀ ε : ℝ, ε > 0 → ...`.

-- Since sequences are function, the `ext` tactic will come in handy. It allows us to prove that functions
-- are equal by showing they are equal at each value.
example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext x y -- The names of the variables are optional
  ring

-- Another useful tactic is `congr`. If the goal is an equality of the form `f x = f y`, it will
-- change the goal to `x = y`.
example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

-- Lastly, the `convert` tactic lets us mix some forward and backwards reasoning. It is similar to the
-- `apply` tactic, but now the goal doesn't need to match the conclusion of the statement we use exactly.
-- Instead, it will create a new goal asking us to show that the two agree.
#check mul_lt_mul_right

example {a : ℝ} (h : 1 < a) : a < a * a := by
  have apos : 0 < a := lt_trans zero_lt_one h
  convert (mul_lt_mul_right apos).2 h -- The term we gave to `convert` has type `1 * a < a * a`.
  -- This doesn't match the goal exactly, but it does if we can show `a = 1 * a`.
  rw [one_mul]

-- Here is a list of lemmas seen in the lectures plus some new ones that you may find useful
-- to complete the exercises. Tactics like `linarith` may already know about some of these.
-- Recall that you can always teach a new lemma to `linarith` by writing `linarith[new_lemma]`


#check lt_of_le_of_ne
#check eq_of_abs_sub_eq_zero
#check abs_nonneg
#check abs_neg
#check abs_add
#check abs_pos
#check add_lt_add
#check abs_mul
#check div_pos
#check mul_lt_mul_right
#check mul_lt_mul_of_pos_left
#check mul_div_cancel
#check mul_div_cancel'
#check ne_of_lt
#check mul_lt_mul
#check mul_lt_mul'
#check mul_lt_mul''


-- 1. Prove the following theorem.
-- Feel free to go back to the relevant workshop sheet, or look in [MIL] or [Tut], if you get stuck!
theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n _
  rw [sub_self, abs_zero]
  exact εpos


-- 2. Understand and finish off the following proof.
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  rw [add_sub_add_comm]
  calc |s n - a + (t n - b)| ≤ |(s n - a)| + |(t n - b)| := abs_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hs _ (le_of_max_le_left hn)) (ht _ (le_of_max_le_right hn))
    _ = ε := by norm_num

-- Hints:

-- You may need some lemmas about `max`. For instance:
#check le_max_left
#check le_of_max_le_left
-- Can you guess what their variants are called?

-- Recall that the tactic `norm_num` can help you simplify expressions involving real numbers.


-- 3. Understand and finish off the following proof.
theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  rcases cs (ε / |c|) (div_pos εpos acpos) with ⟨N, hN⟩
  use N
  intro n hn
  simp_rw [← mul_sub, abs_mul]
  exact (lt_div_iff' acpos).mp (hN n hn)


-- 4. Understand and finish off the following proof.
theorem exists_abs_lt_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  calc |s n| = |s n - a + a| := by rw [sub_add_cancel]
    _ ≤ |s n - a| + |a| := abs_add _ _
    _ < 1 + |a| := add_lt_add_of_lt_of_le (h n hn) (le_refl _)
    _ = |a| + 1 := add_comm _ _

-- 5. Understand and finish off the following proof. You will need this auxiliary lemma for the proof
-- of the final theorem.
lemma aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_lt_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n hn
  simp_rw [sub_zero] at *
  rw [abs_mul]
  by_cases ht : t n = 0
  . rw [ht, abs_zero, mul_zero]
    exact εpos
  calc |s n| * |t n| < B * |t n| := (mul_lt_mul (h₀ _ (le_of_max_le_left hn))
    (le_refl _) (abs_pos.mpr ht) (le_of_lt Bpos))
    _ < B * (ε / B) := mul_lt_mul_of_pos_left (h₁ _ (le_of_max_le_right hn)) Bpos
    _ = ε := mul_div_cancel' _ (ne_of_lt Bpos).symm


-- 6. The final boss!
theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    have : ConvergesTo (fun n ↦ t n - b) 0 := by
      intro ε εpos
      rcases ct ε εpos with ⟨N, hN⟩
      use N
      intro n hn
      rw [sub_zero]
      exact hN n hn
    exact aux cs this
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert this using 1 -- See about `using 1` below.
  . ext n
    ring
  . ring

-- The words `using 1` tell `convert` to not try too hard to match the goal and the conclusion of
-- the statement. In particular, it will look for similarities on a first level. Try changing `1`
-- to a differnet number, or removing `using 1` altogether to see what happens.


-- 7. Bonus round!
theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    simp only [gt_iff_lt, abs_pos, ne_eq, sub_eq_zero]
    exact abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_of_max_le_left (le_refl _))
  have absb : |s N - b| < ε := hNb N (le_of_max_le_right (le_refl _))
  suffices : |a - b| < |a - b|
  . exact lt_irrefl _ this
  calc |a - b| = |(s N - a) + (b - s N)| := by simp only [sub_add_sub_cancel', abs_sub_comm]
    _ ≤ |s N - a| + |b - s N| := abs_add _ _
    _ = |s N - a| + |s N - b| := by simp only [abs_sub_comm]
    _ < ε + ε := add_lt_add absa absb
    _ = |a - b| := by ring
/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Mathlib.Data.Real.Basic
import Library

/-!
# Homework 3: Sequences and convergence
References: [MIL] Mathematics in Lean, [Tut] Tutorials project.
Most of this homework is taken from [MIL 3.6]
-/

/-!
  In this homework you will be proving some basic facts about convergence of sequences of real numbers.
  You will meet some useful tactics along the way!

  For us, as sequence will be same thing as a function `s : ℕ → ℝ`.
-/

-- First, we define what it means for a sequence to converge to a fixed number.
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

-- The notation `∀ ε > 0, ...` is shorthand for `∀ ε : ℝ, ε > 0 → ...`.

-- Since sequences are function, the `ext` tactic will come in handy. It allows us to prove that functions
-- are equal by showing they are equal at each value.
example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext x y -- The names of the variables are optional
  ring

-- Another useful tactic is `congr`. If the goal is an equality of the form `f x = f y`, it will
-- change the goal to `x = y`.
example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

-- Lastly, the `convert` tactic lets us mix some forward and backwards reasoning. It is similar to the
-- `apply` tactic, but now the goal doesn't need to match the conclusion of the statement we use exactly.
-- Instead, it will create a new goal asking us to show that the two agree.
#check mul_lt_mul_right

example {a : ℝ} (h : 1 < a) : a < a * a := by
  have apos : 0 < a := lt_trans zero_lt_one h
  convert (mul_lt_mul_right apos).2 h -- The term we gave to `convert` has type `1 * a < a * a`.
  -- This doesn't match the goal exactly, but it does if we can show `a = 1 * a`.
  rw [one_mul]

-- Here is a list of lemmas seen in the lectures plus some new ones that you may find useful
-- to complete the exercises. Tactics like `linarith` may already know about some of these.
-- Recall that you can always teach a new lemma to `linarith` by writing `linarith[new_lemma]`


#check lt_of_le_of_ne
#check eq_of_abs_sub_eq_zero
#check abs_nonneg
#check abs_neg
#check abs_add
#check abs_pos
#check add_lt_add
#check abs_mul
#check div_pos
#check mul_lt_mul_right
#check mul_lt_mul_of_pos_left
#check mul_div_cancel
#check mul_div_cancel'
#check ne_of_lt
#check mul_lt_mul
#check mul_lt_mul'
#check mul_lt_mul''


-- 1. Prove the following theorem.
-- Feel free to go back to the relevant workshop sheet, or look in [MIL] or [Tut], if you get stuck!
theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n _
  rw [sub_self, abs_zero]
  exact εpos


-- 2. Understand and finish off the following proof.
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  rw [add_sub_add_comm]
  calc |s n - a + (t n - b)| ≤ |(s n - a)| + |(t n - b)| := abs_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hs _ (le_of_max_le_left hn)) (ht _ (le_of_max_le_right hn))
    _ = ε := by norm_num

-- Hints:

-- You may need some lemmas about `max`. For instance:
#check le_max_left
#check le_of_max_le_left
-- Can you guess what their variants are called?

-- Recall that the tactic `norm_num` can help you simplify expressions involving real numbers.


-- 3. Understand and finish off the following proof.
theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  rcases cs (ε / |c|) (div_pos εpos acpos) with ⟨N, hN⟩
  use N
  intro n hn
  simp_rw [← mul_sub, abs_mul]
  exact (lt_div_iff' acpos).mp (hN n hn)


-- 4. Understand and finish off the following proof.
theorem exists_abs_lt_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  calc |s n| = |s n - a + a| := by rw [sub_add_cancel]
    _ ≤ |s n - a| + |a| := abs_add _ _
    _ < 1 + |a| := add_lt_add_of_lt_of_le (h n hn) (le_refl _)
    _ = |a| + 1 := add_comm _ _

-- 5. Understand and finish off the following proof. You will need this auxiliary lemma for the proof
-- of the final theorem.
lemma aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_lt_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n hn
  simp_rw [sub_zero] at *
  rw [abs_mul]
  by_cases ht : t n = 0
  . rw [ht, abs_zero, mul_zero]
    exact εpos
  calc |s n| * |t n| < B * |t n| := (mul_lt_mul (h₀ _ (le_of_max_le_left hn))
    (le_refl _) (abs_pos.mpr ht) (le_of_lt Bpos))
    _ < B * (ε / B) := mul_lt_mul_of_pos_left (h₁ _ (le_of_max_le_right hn)) Bpos
    _ = ε := mul_div_cancel' _ (ne_of_lt Bpos).symm


-- 6. The final boss!
theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    have : ConvergesTo (fun n ↦ t n - b) 0 := by
      intro ε εpos
      rcases ct ε εpos with ⟨N, hN⟩
      use N
      intro n hn
      rw [sub_zero]
      exact hN n hn
    exact aux cs this
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert this using 1 -- See about `using 1` below.
  . ext n
    ring
  . ring

-- The words `using 1` tell `convert` to not try too hard to match the goal and the conclusion of
-- the statement. In particular, it will look for similarities on a first level. Try changing `1`
-- to a differnet number, or removing `using 1` altogether to see what happens.


-- 7. Bonus round!
theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    simp only [gt_iff_lt, abs_pos, ne_eq, sub_eq_zero]
    exact abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_of_max_le_left (le_refl _))
  have absb : |s N - b| < ε := hNb N (le_of_max_le_right (le_refl _))
  suffices : |a - b| < |a - b|
  . exact lt_irrefl _ this
  calc |a - b| = |(s N - a) + (b - s N)| := by simp only [sub_add_sub_cancel', abs_sub_comm]
    _ ≤ |s N - a| + |b - s N| := abs_add _ _
    _ = |s N - a| + |s N - b| := by simp only [abs_sub_comm]
    _ < ε + ε := add_lt_add absa absb
    _ = |a - b| := by ring
/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Mathlib.Data.Real.Basic
import Library

/-!
# Homework 3: Sequences and convergence
References: [MIL] Mathematics in Lean, [Tut] Tutorials project.
Most of this homework is taken from [MIL 3.6]
-/

/-!
  In this homework you will be proving some basic facts about convergence of sequences of real numbers.
  You will meet some useful tactics along the way!

  For us, as sequence will be same thing as a function `s : ℕ → ℝ`.
-/

-- First, we define what it means for a sequence to converge to a fixed number.
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

-- The notation `∀ ε > 0, ...` is shorthand for `∀ ε : ℝ, ε > 0 → ...`.

-- Since sequences are function, the `ext` tactic will come in handy. It allows us to prove that functions
-- are equal by showing they are equal at each value.
example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext x y -- The names of the variables are optional
  ring

-- Another useful tactic is `congr`. If the goal is an equality of the form `f x = f y`, it will
-- change the goal to `x = y`.
example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

-- Lastly, the `convert` tactic lets us mix some forward and backwards reasoning. It is similar to the
-- `apply` tactic, but now the goal doesn't need to match the conclusion of the statement we use exactly.
-- Instead, it will create a new goal asking us to show that the two agree.
#check mul_lt_mul_right

example {a : ℝ} (h : 1 < a) : a < a * a := by
  have apos : 0 < a := lt_trans zero_lt_one h
  convert (mul_lt_mul_right apos).2 h -- The term we gave to `convert` has type `1 * a < a * a`.
  -- This doesn't match the goal exactly, but it does if we can show `a = 1 * a`.
  rw [one_mul]

-- Here is a list of lemmas seen in the lectures plus some new ones that you may find useful
-- to complete the exercises. Tactics like `linarith` may already know about some of these.
-- Recall that you can always teach a new lemma to `linarith` by writing `linarith[new_lemma]`


#check lt_of_le_of_ne
#check eq_of_abs_sub_eq_zero
#check abs_nonneg
#check abs_neg
#check abs_add
#check abs_pos
#check add_lt_add
#check abs_mul
#check div_pos
#check mul_lt_mul_right
#check mul_lt_mul_of_pos_left
#check mul_div_cancel
#check mul_div_cancel'
#check ne_of_lt
#check mul_lt_mul
#check mul_lt_mul'
#check mul_lt_mul''


-- 1. Prove the following theorem.
-- Feel free to go back to the relevant workshop sheet, or look in [MIL] or [Tut], if you get stuck!
theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n _
  rw [sub_self, abs_zero]
  exact εpos


-- 2. Understand and finish off the following proof.
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  rw [add_sub_add_comm]
  calc |s n - a + (t n - b)| ≤ |(s n - a)| + |(t n - b)| := abs_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hs _ (le_of_max_le_left hn)) (ht _ (le_of_max_le_right hn))
    _ = ε := by norm_num

-- Hints:

-- You may need some lemmas about `max`. For instance:
#check le_max_left
#check le_of_max_le_left
-- Can you guess what their variants are called?

-- Recall that the tactic `norm_num` can help you simplify expressions involving real numbers.


-- 3. Understand and finish off the following proof.
theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  rcases cs (ε / |c|) (div_pos εpos acpos) with ⟨N, hN⟩
  use N
  intro n hn
  simp_rw [← mul_sub, abs_mul]
  exact (lt_div_iff' acpos).mp (hN n hn)


-- 4. Understand and finish off the following proof.
theorem exists_abs_lt_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  calc |s n| = |s n - a + a| := by rw [sub_add_cancel]
    _ ≤ |s n - a| + |a| := abs_add _ _
    _ < 1 + |a| := add_lt_add_of_lt_of_le (h n hn) (le_refl _)
    _ = |a| + 1 := add_comm _ _

-- 5. Understand and finish off the following proof. You will need this auxiliary lemma for the proof
-- of the final theorem.
lemma aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_lt_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n hn
  simp_rw [sub_zero] at *
  rw [abs_mul]
  by_cases ht : t n = 0
  . rw [ht, abs_zero, mul_zero]
    exact εpos
  calc |s n| * |t n| < B * |t n| := (mul_lt_mul (h₀ _ (le_of_max_le_left hn))
    (le_refl _) (abs_pos.mpr ht) (le_of_lt Bpos))
    _ < B * (ε / B) := mul_lt_mul_of_pos_left (h₁ _ (le_of_max_le_right hn)) Bpos
    _ = ε := mul_div_cancel' _ (ne_of_lt Bpos).symm


-- 6. The final boss!
theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    have : ConvergesTo (fun n ↦ t n - b) 0 := by
      intro ε εpos
      rcases ct ε εpos with ⟨N, hN⟩
      use N
      intro n hn
      rw [sub_zero]
      exact hN n hn
    exact aux cs this
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert this using 1 -- See about `using 1` below.
  . ext n
    ring
  . ring

-- The words `using 1` tell `convert` to not try too hard to match the goal and the conclusion of
-- the statement. In particular, it will look for similarities on a first level. Try changing `1`
-- to a differnet number, or removing `using 1` altogether to see what happens.


-- 7. Bonus round!
theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    simp only [gt_iff_lt, abs_pos, ne_eq, sub_eq_zero]
    exact abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_of_max_le_left (le_refl _))
  have absb : |s N - b| < ε := hNb N (le_of_max_le_right (le_refl _))
  suffices : |a - b| < |a - b|
  . exact lt_irrefl _ this
  calc |a - b| = |(s N - a) + (b - s N)| := by simp only [sub_add_sub_cancel', abs_sub_comm]
    _ ≤ |s N - a| + |b - s N| := abs_add _ _
    _ = |s N - a| + |s N - b| := by simp only [abs_sub_comm]
    _ < ε + ε := add_lt_add absa absb
    _ = |a - b| := by ring
/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Mathlib.Data.Real.Basic
import Library

/-!
# Homework 3: Sequences and convergence
References: [MIL] Mathematics in Lean, [Tut] Tutorials project.
Most of this homework is taken from [MIL 3.6]
-/

/-!
  In this homework you will be proving some basic facts about convergence of sequences of real numbers.
  You will meet some useful tactics along the way!

  For us, as sequence will be same thing as a function `s : ℕ → ℝ`.
-/

-- First, we define what it means for a sequence to converge to a fixed number.
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

-- The notation `∀ ε > 0, ...` is shorthand for `∀ ε : ℝ, ε > 0 → ...`.

-- Since sequences are function, the `ext` tactic will come in handy. It allows us to prove that functions
-- are equal by showing they are equal at each value.
example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext x y -- The names of the variables are optional
  ring

-- Another useful tactic is `congr`. If the goal is an equality of the form `f x = f y`, it will
-- change the goal to `x = y`.
example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

-- Lastly, the `convert` tactic lets us mix some forward and backwards reasoning. It is similar to the
-- `apply` tactic, but now the goal doesn't need to match the conclusion of the statement we use exactly.
-- Instead, it will create a new goal asking us to show that the two agree.
#check mul_lt_mul_right

example {a : ℝ} (h : 1 < a) : a < a * a := by
  have apos : 0 < a := lt_trans zero_lt_one h
  convert (mul_lt_mul_right apos).2 h -- The term we gave to `convert` has type `1 * a < a * a`.
  -- This doesn't match the goal exactly, but it does if we can show `a = 1 * a`.
  rw [one_mul]

-- Here is a list of lemmas seen in the lectures plus some new ones that you may find useful
-- to complete the exercises. Tactics like `linarith` may already know about some of these.
-- Recall that you can always teach a new lemma to `linarith` by writing `linarith[new_lemma]`


#check lt_of_le_of_ne
#check eq_of_abs_sub_eq_zero
#check abs_nonneg
#check abs_neg
#check abs_add
#check abs_pos
#check add_lt_add
#check abs_mul
#check div_pos
#check mul_lt_mul_right
#check mul_lt_mul_of_pos_left
#check mul_div_cancel
#check mul_div_cancel'
#check ne_of_lt
#check mul_lt_mul
#check mul_lt_mul'
#check mul_lt_mul''


-- 1. Prove the following theorem.
-- Feel free to go back to the relevant workshop sheet, or look in [MIL] or [Tut], if you get stuck!
theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n _
  rw [sub_self, abs_zero]
  exact εpos


-- 2. Understand and finish off the following proof.
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  rw [add_sub_add_comm]
  calc |s n - a + (t n - b)| ≤ |(s n - a)| + |(t n - b)| := abs_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hs _ (le_of_max_le_left hn)) (ht _ (le_of_max_le_right hn))
    _ = ε := by norm_num

-- Hints:

-- You may need some lemmas about `max`. For instance:
#check le_max_left
#check le_of_max_le_left
-- Can you guess what their variants are called?

-- Recall that the tactic `norm_num` can help you simplify expressions involving real numbers.


-- 3. Understand and finish off the following proof.
theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  rcases cs (ε / |c|) (div_pos εpos acpos) with ⟨N, hN⟩
  use N
  intro n hn
  simp_rw [← mul_sub, abs_mul]
  exact (lt_div_iff' acpos).mp (hN n hn)


-- 4. Understand and finish off the following proof.
theorem exists_abs_lt_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  calc |s n| = |s n - a + a| := by rw [sub_add_cancel]
    _ ≤ |s n - a| + |a| := abs_add _ _
    _ < 1 + |a| := add_lt_add_of_lt_of_le (h n hn) (le_refl _)
    _ = |a| + 1 := add_comm _ _

-- 5. Understand and finish off the following proof. You will need this auxiliary lemma for the proof
-- of the final theorem.
lemma aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_lt_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n hn
  simp_rw [sub_zero] at *
  rw [abs_mul]
  by_cases ht : t n = 0
  . rw [ht, abs_zero, mul_zero]
    exact εpos
  calc |s n| * |t n| < B * |t n| := (mul_lt_mul (h₀ _ (le_of_max_le_left hn))
    (le_refl _) (abs_pos.mpr ht) (le_of_lt Bpos))
    _ < B * (ε / B) := mul_lt_mul_of_pos_left (h₁ _ (le_of_max_le_right hn)) Bpos
    _ = ε := mul_div_cancel' _ (ne_of_lt Bpos).symm


-- 6. The final boss!
theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    have : ConvergesTo (fun n ↦ t n - b) 0 := by
      intro ε εpos
      rcases ct ε εpos with ⟨N, hN⟩
      use N
      intro n hn
      rw [sub_zero]
      exact hN n hn
    exact aux cs this
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert this using 1 -- See about `using 1` below.
  . ext n
    ring
  . ring

-- The words `using 1` tell `convert` to not try too hard to match the goal and the conclusion of
-- the statement. In particular, it will look for similarities on a first level. Try changing `1`
-- to a differnet number, or removing `using 1` altogether to see what happens.


-- 7. Bonus round!
theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    simp only [gt_iff_lt, abs_pos, ne_eq, sub_eq_zero]
    exact abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_of_max_le_left (le_refl _))
  have absb : |s N - b| < ε := hNb N (le_of_max_le_right (le_refl _))
  suffices : |a - b| < |a - b|
  . exact lt_irrefl _ this
  calc |a - b| = |(s N - a) + (b - s N)| := by simp only [sub_add_sub_cancel', abs_sub_comm]
    _ ≤ |s N - a| + |b - s N| := abs_add _ _
    _ = |s N - a| + |s N - b| := by simp only [abs_sub_comm]
    _ < ε + ε := add_lt_add absa absb
    _ = |a - b| := by ring
