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

-- Use `List.concat` to recursively a function takes a list and reverses it.
def reverse : List α → List α
  | [] => []
  | head :: tail => List.concat (reverse tail) head


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


-- Finally, we can talk about `Finset`. It is a structure (inductive type with on constructor)
-- that packages a multiset with a proof that it has no duplicates.
#check Finset

-- The most common `Finset`s are ranges of natural numbers (think indexing sets of summations).
-- This are constructed with `Finset.range`.
#eval Finset.range 5

-- The good news is that there are a lot of lemmas about `Finset` that let us forget its
-- complicated definition as a subtype of `Multiset`.

open BigOperators

-- For example, try to prove the following well-known formula.
-- The notation for a sum should be self explanatory, otherwise `ctrl/cmd + click` or hover over it
-- to see a helpful documenation comment.

-- You will want to use things like:
#check Finset.sum_range_zero
#check Finset.sum_range_succ

lemma sum_range (n : ℕ) : ∑ i in Finset.range n, (↑i : ℚ) = ↑n * (n - 1) / 2 := sorry



end Hidden


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
-- one term. You can `ctrl/cmd + click` on `Nonempty` to see its definition.
#check Nonempty

-- Given that it is an inductive type, do you see how you could use and construct a term of
-- type `Nonempty α` for some type `α`? Try the following:

example : Nonempty ℕ := sorry

example {α β : Type} : Nonempty α → Nonempty β → Nonempty (α × β) := sorry

-- Now try to understand and prove the following lemma.
lemma existence_implies_everything_iff {α : Type*} (r : α → Prop) :
  (∃ x, (r x → ∀ y, r y)) ↔ Nonempty α := sorry

-- You can think of `Nonempty` as a special case of `Exists` (`∃`), where the predicate is trivial.


/-
  ## Q3: Type equality and cardinality
  For this question, we will explore when two types can be the same in two different ways.
  One of them is equality, which is very strict. Another is having the same cardinality.
-/

-- Two types being equal is a very strong statement. For example, if `α` and `β` are equal, then
-- any term of type `α` can be used as a term of type `β`.

-- Conversely, if `x : α` and `x : β` then `α = β`. This is not something we can prove,
-- it is a syntactical necessity.

-- We can however prove that two types are not equal, if they satisfy different properties.
lemma ne_types_of_different_property {α β : Type}
  (p : Type → Prop) (hα : p α) (hβ : ¬ p β) : α ≠ β := sorry

-- Now prove that there exists two types that are not equal.
lemma exists_ne_types : ∃ α β : Type, α ≠ β := sorry
-- If you get stuck at this point, skip this exercise and come back to it at the end!

section

/-
  Types can be related in other ways other than being equal. For example, mathlib defines
  a type `Cardinal` which is a quotient of `Type` by the equivalence relation of having the same
  cardinality. Two types have the same cardinality if there exists a bijection between them.
-/

-- `ctrl/cmd + click` through to examine the definitions.
#check Cardinal
-- Note how `Nonempty` is used in the definition of `Cardinal`.

-- There are also types that witness when a type is countable or uncountable.
#check Countable
#check Uncountable
-- These are defined as classes, which we haven't seen yet, but you can just think of them as
-- inductive types with only one constructor for now.

-- Mathlib defines the convenient notation `#α` for the cardinal corresponding to a type `α`.
-- To access it `#` we need to open the `Cardinal` namespace.
open Cardinal

section
variable {α : Type}

#check #α
-- This is the same as `Quotient.mk Cardinal.isEquivalent α`.
end

-- Now prove that two types with different cardinality cannot be equal.
lemma ne_types_of_ne_cardinal {α β : Type} (h : #α ≠ #β) : α ≠ β := by
  sorry

-- Now prove this. (Hint: you don't need to use the previous one.)
lemma ne_types_of_countable_uncountable {α β : Type}
  (hα : Countable α) (hβ : Uncountable β) : α ≠ β := sorry

-- *Reminder*: if you couldn't find two types that were not equal before, go back a try it now.

end


/-
  ## Q4: Nat.cast is not surjective
  For this last question, we will prove that the obvious inclusion `ℕ → ℤ` is not surjective.
  In Lean, this inclusion is called `Nat.cast`.
-/

#check Nat.cast (R := ℤ)
-- Cast is defined in greater generality as a function `ℕ → R` for certain types `R`. This
-- argument is implicit, but we can provide it explicilty using the `(R := ℤ)` syntax.
#check Nat.cast (R := ℤ) 0
-- Note that Lean uses the `↑` notation for `Nat.cast`. We will learn more about this next week.

lemma not_surjective_nat_int : ¬ Function.Surjective (Nat.cast : ℕ → ℤ) := sorry

-- You may find the following lemma useful.
#check Nat.cast_lt (α := ℤ)
