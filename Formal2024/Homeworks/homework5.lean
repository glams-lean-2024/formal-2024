/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Library

/-!
  # Homework 5: More on induction and types
  References: [MIL] Mathematics in Lean, [Tut] Tutorials project.
  This week we will also use the textbook [TPL] Theorem Proving in Lean 4, which can
  be found at https://leanprover.github.io/theorem_proving_in_lean4/
-/

/-
  ## Q1: Infinitely many primes
  In this question, we will define the factorial operation on `ℕ` and use it to prove that
  there are infinitely many prime numbers. Recall that tactics like `norm_num` or `linarith`
  are your friends!
-/

-- Here is the definition.
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

-- Start by proving that `n ≤ n!`.
lemma le_fac_self (n : ℕ) : n ≤ fac n := sorry

-- Now prove that any natural number between `1` and `n` divides `fac n`.
lemma dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := sorry

-- You may find the following useful.
#check Nat.of_le_succ
#check dvd_mul_of_dvd_right
#check dvd_mul_right

-- Now use `le_fac_self`, `dvd_fac` and `Nat.exists_prime_and_dvd` to prove that there are
-- infinitely many primes.
#check Nat.exists_prime_and_dvd

theorem exists_prime_ge (n : ℕ) : ∃ p, p > n ∧ Nat.Prime p := sorry


/-
  ## Q2: Other kinds of induction
  Sometimes, we want to do induction on `ℕ` but starting from something other than `0`.
  The lemma `Nat.le_induction` is useful for this, but using it can be a bit tricky.
-/

-- Try proving this by regular induction on `n`. You will see that it is not so easy.
example (x : ℝ) (n : ℕ) (hx : x ≥ 2) (hn : n ≥ 1) : x ^ n ≥ n * x := sorry

-- Instead, we want to use this lemma. If you `ctrl/cmd + click` through you will see a
-- short documentation comment describing its use.
#check Nat.le_induction

-- Now try proving it using `Nat.le_induction`.
example (x : ℝ) (n : ℕ) (hx : x ≥ 2) (hn : n ≥ 1) : x ^ n ≥ n * x := by
  induction' n, hn using Nat.le_induction with n hn ih generalizing x
  -- `generalizing x` makes is so that `x` is not fixed in the induction hypothesis.
  · sorry
  sorry


/-
  ## Q3: Lists, multisets and finite sets
  Last week we saw that given a type `α`, the type `Set α` is the type of subsets of `α`.
  We can also do this just for finite subsets, using the `Finset` type. However, `Finset` is
  defined in a much more complicated way than `Set`.
-/

namespace Hidden

-- Internally, a term of `Finset α` is a list of distinct elements of `α` up to permuation.
-- This uses inductive types and quotients at the same time!

-- First, let's get a little acquainted with the `List` type.
-- Use `ctrl/cmd + click` to see the definition of `List` as an inductive type.
#check List
-- What are its constructors? What are they doing?

variable {α : Type}

-- The constructors for `List` have alternative notations.
example : [] = (List.nil : List α) := rfl
example : 0 :: [] = List.cons 0 List.nil := rfl
-- You can also use the familiar notation from other programming languages.
#check [0, 1, 2]

-- As you can see, lists are built inductively by adding elements at the beginning.
-- `List.concat` gives us the operation of adding an element at the end.
#check List.concat
#eval List.concat [0] 1

-- Use `List.concat` to recursively define a function takes a list and reverses it.
def reverse : List α → List α
  | [] => sorry
  | head :: tail => sorry


-- `List` has the structure of a `Setoid`, where two lists are related if they are permuations
-- of each other. This equivalence relation is called `List.Perm`, and it is defined inductively.
-- Check it out!
#check List.isSetoid
#check List.Perm

-- For convenience, here a copy of the definition of `List.Perm`:
inductive MyPerm : List α → List α → Prop
  /-- `[] ~ []` -/
  | nil : MyPerm [] []
  /-- `l₁ ~ l₂ → x::l₁ ~ x::l₂` -/
  | cons (x : α) {l₁ l₂ : List α} : MyPerm l₁ l₂ → MyPerm (x :: l₁) (x :: l₂)
  /-- `x::y::l ~ y::x::l` -/
  | swap (x y : α) (l : List α) : MyPerm (y :: x :: l) (x :: y :: l)
  /-- `Perm` is transitive. -/
  | trans {l₁ l₂ l₃ : List α} : MyPerm l₁ l₂ → MyPerm l₂ l₃ → MyPerm l₁ l₃


-- Try to prove that the reverse of a list is a permutation of the original list.
-- You may want to use:
#check List.concat_perm

lemma reverse_perm (l : List α) : List.Perm l (reverse l) := sorry


-- Now let's move on to `Multiset`. This is the quotient of the `List` type by the `List.Perm`
-- relation.
#check Multiset

-- Use `reverse_perm` to show that the reverse of a multiset stays the same.
-- You will want to use `Quot.sound`.
lemma reverse_multiset (l : List α) : Multiset.ofList l = Multiset.ofList (reverse l) := sorry

end Hidden

-- Finally, we can talk about `Finset`. It is a structure (inductive type with one constructor)
-- that packages a multiset with a proof that it has no duplicates.
#check Finset

-- The most common `Finset`s are ranges of natural numbers (e.g., as indexing sets of summations).
-- These are constructed with `Finset.range`.
#eval Finset.range 5

-- The good news is that there are a lot of lemmas about `Finset` that let us forget its
-- complicated definition as a subtype of `Multiset`.

open BigOperators

-- For example, try to prove the following well-known formula.
-- The notation for a sum should be self-explanatory, otherwise `ctrl/cmd + click` or hover over it
-- to see a helpful documentation comment.

-- You will want to use things like:
#check Finset.sum_range_zero
#check Finset.sum_range_succ

lemma sum_range (n : ℕ) : ∑ i in Finset.range n, (↑i : ℚ) = ↑n * (n - 1) / 2 := sorry
