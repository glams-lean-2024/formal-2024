/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Library

/-!

# Exercises for week 5

-/


/-! ## Part 1 : myEven and myOdd
  definitions of myEven and myOdd natural numbers using `inductive` -/

inductive myEven : Nat → Prop
| zero : myEven 0
| two_plus_n : ∀ n, myEven n → myEven (n + 2)

inductive myOdd : Nat → Prop
| one : myOdd 1
| two_plus_n : ∀ n, myOdd n → myOdd (n + 2)

/-! ### basic properties of myEven and myOdd -/

theorem myEven_or_myOdd : ∀ n, myEven n ∨ myOdd n := sorry

theorem myOdd_succ_myEven : ∀ n, myOdd n → myEven (n + 1) := sorry

theorem myEven_succ_myOdd : ∀ n, myEven n → myOdd (n + 1) := sorry

/-! ### addition -/

theorem myEven_add_myOdd : ∀ m n, myEven m → myOdd n → myOdd (m + n) := sorry

theorem myOdd_add_myEven : ∀ m n, myOdd m → myEven n → myOdd (m + n) := sorry

theorem myOdd_add_myOdd : ∀ m n, myOdd m → myOdd n → myEven (m + n) := sorry

theorem myEven_add_myEven : ∀ m n, myEven m → myEven n → myEven (m + n) := sorry

/-! ### multiplication -/

theorem myEven_mul : ∀ m n, myEven m → myEven (m * n) := sorry

theorem mul_myEven : ∀ m n, myEven n → myEven (m * n) := sorry

theorem myOdd_mul_myOdd : ∀ m n, myOdd m → myOdd n → myOdd (m * n) := sorry

/-! ### power -/

theorem myEven_pow : ∀ m n, myEven m → myEven (m ^ n) := sorry

theorem myOdd_pow : ∀ m n, myOdd m → myOdd (m ^ n) := sorry


/-! ## Part 2 : Unique existence
  We introduce the useful `∃!` notation. Given a type `α` and `p : α → Prop`, `∃! x : α, p x` is
  a proposition asserting that there exists a unique term `x : α` such that `p x` holds.
  This is equivalent to `∃ x, p x ∧ ∀ y, p y → y = x`.
-/

-- Examine the following example to see how `∃!` is defined; then try to prove it.
example : ∃! x : ℕ, x = 0 := by
  dsimp [ExistsUnique]
  sorry

-- The `∃!` notation can take several variables, but this can be quite confusing.
-- For example, try to understand what the following lemma is saying, and then prove it.
lemma Nat.exists_unique_le : ∃! n m : Nat, m ≤ n := by
  sorry


/-! ## Part 3 : Types and logic
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
theorem existence_implies_everything_iff {α : Type*} (r : α → Prop) :
  (∃ x, (r x → ∀ y, r y)) ↔ Nonempty α := sorry

-- The above theorem is exactly "drinker's principle/paradox": [wiki/drinker_paradox#non-empty_domain](https://en.wikipedia.org/wiki/Drinker_paradox#Non-empty_domain).

-- You can think of `Nonempty` as a special case of `Exists` (`∃`), where the predicate is trivial.


/-! ## Part 4 : Type equality and cardinality
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
theorem exists_ne_types : ∃ α β : Type, α ≠ β := sorry
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

-- Now prove that two types where one is countable and one isn't cannot be equal.
lemma ne_types_of_countable_uncountable {α β : Type}
  (hα : Countable α) (hβ : Uncountable β) : α ≠ β := sorry

-- Now prove this. (Hint: you don't need to use the previous one.)
lemma ne_types_of_ne_cardinal {α β : Type} (h : #α ≠ #β) : α ≠ β := by
  sorry

-- *Reminder*: if you couldn't find two types that were not equal before, go back to theorem `exists_ne_types` a try it now.

end


/-! ## Part 5 : Nat.cast is not surjective
  For this last question, we will prove that the obvious inclusion `ℕ → ℤ` is not surjective.
  In Lean, this inclusion is called `Nat.cast`.
-/

open Function

#check Nat.cast (α := ℤ)
-- Cast is defined in greater generality as a function `ℕ → α` for certain types `α`. This
-- argument is implicit, but we can provide it explicitly using the `(α := ℤ)` syntax.
#check Nat.cast (α := ℤ) 0
-- Note that Lean uses the `↑` notation for `Nat.cast`. We will learn more about this next week.

lemma not_surjective_nat_int : ¬ Surjective (Nat.cast : ℕ → ℤ) := sorry

-- You may find the following lemma useful.
#check Nat.cast_lt (α := ℤ)
