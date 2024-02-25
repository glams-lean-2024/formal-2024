import Library

/-! # Part 1 : myEven and myOdd
  definitions of myEven and myOdd natural numbers using `inductive` -/

inductive myEven : Nat → Prop
| zero : myEven 0
| two_plus_n : ∀ n, myEven n → myEven (n + 2)

inductive myOdd : Nat → Prop
| one : myOdd 1
| two_plus_n : ∀ n, myOdd n → myOdd (n + 2)

/-! ## basic properties of myEven and myOdd -/

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

/-! # Part 2 : uniqueness of natural numbers with `≤`

  `∃! x` is notation for "there exists a unique `x`".
  This is equivalent to `∃ x, p x ∧ ∀ y, p y → y = x`.

  This can be confusing when involving more variables, so we will prove the following.
-/

theorem Nat.exists_unique_le : ∃! n m : Nat, m ≤ n := sorry

/-! # Part 3 : existence implies everything (if and only if the universe is nonempty)
  in other words, if we know something exists, then everything exists -/

theorem existence_implies_everything_iff {α : Type*} (r : α → Prop) :
  (∃ x, (r x → ∀ y, r y)) ↔ Nonempty α := sorry

section Part_4
/-! # Part 4 : non-equal types

Firstly, some definitions:
* `Cardinal` is a structure that represents the cardinality of a type.
  We can use it to compare the cardinality of two types.
  In order to use the notation `#α`, which exactly means "the cardinality of `α`", we need to `open Cardinal` first.
* `Countable α` is defined as `Prop`, which is determined by whether there exists an injective map `α → ℕ`.
* `Uncountable α` is defined as `¬ (Countable α)`.


We will prove the following lemmas and theorems about non-equal types.

* `ne_types_of_ne_cardinal`: we have non-equal types given their cardinality is non-equal

* `ne_types_of_countable_uncountable`: if a type is countable and the other isn't, then they are non-equal

* `ne_types_of_different_property`: generalising the above two,
    we get non-equal types given there is a different property

an easy example of all of this is the following.
* `exists_ne_types`: there exists two types that are non-equal
-/

open Cardinal

lemma ne_types_of_ne_cardinal {α β : Type} (h : #α ≠ #β) : α ≠ β := sorry

lemma ne_types_of_countable_uncountable {α β : Type}
  (hα : Countable α) (hβ : Uncountable β) : α ≠ β := sorry

theorem ne_types_of_different_property {α β : Type}
  (p : Type → Prop) (hα : p α) (hβ : ¬ p β) : α ≠ β := sorry

example : ∃ α β : Type, α ≠ β := sorry

end Part_4

/-! # Part 5 : Nat.cast is not surjective -/

theorem Nat.cast_is_not_surjective : ¬ Function.Surjective (Nat.cast : ℕ → ℤ) := sorry
