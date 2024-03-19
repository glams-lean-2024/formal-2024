/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Library

/-!

# Exercises for week 5

-/


section
/-! ## Part 1 : myEven and myOdd
  definitions of myEven and myOdd natural numbers using `inductive` -/


inductive myEven : Nat → Prop
| zero : myEven 0
| two_plus_n : ∀ n, myEven n → myEven (n + 2)

inductive myOdd : Nat → Prop
| one : myOdd 1
| two_plus_n : ∀ n, myOdd n → myOdd (n + 2)

/-! ### basic properties of myEven and myOdd -/


open myEven myOdd

-- reordered results
theorem myOdd_succ_myEven : ∀ n, myOdd n → myEven (n + 1) := λ n hn => by
induction hn with
| one => exact two_plus_n 0 zero
| two_plus_n n _ hhn => exact two_plus_n _ hhn

theorem myEven_succ_myOdd : ∀ n, myEven n → myOdd (n + 1) := λ n hn => by
induction hn with
| zero => exact myOdd.one
| two_plus_n n _ hhn => exact two_plus_n _ hhn

theorem myEven_or_myOdd : ∀ n, myEven n ∨ myOdd n := λ n => by induction n with
| zero => exact Or.inl zero
| succ _ hd =>
  rcases hd with (hd|hd)
  { exact Or.inr (myEven_succ_myOdd _ hd) }
  { exact Or.inl (myOdd_succ_myEven _ hd) }

/-! ### addition -/

theorem myEven_add_myOdd : ∀ m n, myEven m → myOdd n → myOdd (m + n) := λ m n hm hn => by
induction hn with
| one => exact myEven_succ_myOdd _ hm
| two_plus_n _ _ hm => rw [← add_assoc]; exact two_plus_n _ hm

theorem myOdd_add_myEven : ∀ m n, myOdd m → myEven n → myOdd (m + n) := λ m n hm hn => by
rw [add_comm]; exact myEven_add_myOdd _ _ hn hm

theorem myOdd_add_myOdd : ∀ m n, myOdd m → myOdd n → myEven (m + n) := λ m n hm hn => by
induction hn with
| one => exact myOdd_succ_myEven _ hm
| _ _ _ hm => rw [← add_assoc]; exact two_plus_n _ hm

theorem myEven_add_myEven : ∀ m n, myEven m → myEven n → myEven (m + n) := λ m n hm hn => by
induction hn with
| zero => exact hm
| _ _ _ hn => rw [← add_assoc]; exact two_plus_n _ hn

/-! ### multiplication -/

lemma myEven_two_mul {n : ℕ} :
  myEven (2 * n) := by
induction n with | zero => exact zero | _ _ hd => rw [Nat.mul_succ]; exact two_plus_n _ hd

theorem myEven_mul : ∀ m n, myEven m → myEven (m * n) := λ m n hm => by
induction hm with
| zero => rw [zero_mul]; exact zero
| _ _ _ hn => rw [add_mul]; exact myEven_add_myEven _ _ hn myEven_two_mul

theorem mul_myEven : ∀ m n, myEven n → myEven (m * n) := λ m n hn => by
rw [mul_comm]; exact myEven_mul _ _ hn

theorem myOdd_mul_myOdd : ∀ m n, myOdd m → myOdd n → myOdd (m * n) := λ m n hm hn => by
induction hn with
| one => rw [mul_one]; exact hm
| _ _ _ hn => rw [mul_add, mul_comm _ 2]; exact myOdd_add_myEven _ _ hn myEven_two_mul

/-! ### power -/

-- forgot to say that `n : ℕˣ`
theorem myEven_pow : ∀ m (n : ℕˣ), myEven m → (myEven (m ^ (n : ℕ))) := λ m n hm => by
-- changing `n : ℕˣ` to `n' : ℕ` instead of having coercions everywhere
let n' : ℕ := n; have : n' = n := rfl; simp only [← this, Ne.def] at *; clear this
have hnn : 1 ≤ n' := Nat.one_le_iff_ne_zero.mpr (n.ne_zero)
-- `revert` so that `n'` can be replaced in `hnn` as well
revert hnn
induction n' with
| zero => intro; contradiction
| succ _ _ => rw [pow_succ']; exact λ _ => mul_myEven _ _ hm

-- also forgot to say that `n : ℕˣ` here
theorem myOdd_pow : ∀ m (n : ℕˣ), myOdd m → myOdd (m ^ (n : ℕ)) := λ m n hm => by
-- changing `n : ℕˣ` to `n' : ℕ` instead of having coercions everywhere
let n' : ℕ := n; have : n' = n := rfl; simp only [← this, Ne.def] at *; clear this
have hnn : 1 ≤ n' := Nat.one_le_iff_ne_zero.mpr (n.ne_zero)
-- `revert` so that `n'` can be replaced in `hnn` as well
revert hnn
induction n' with
| zero => intro; contradiction
| succ _ hd =>
  { intro hn
    rcases Nat.le_or_eq_of_le_succ hn with (h | h)
    { rw [pow_succ']
      exact myOdd_mul_myOdd _ _ (hd h) hm }
    { rw [← h, pow_one]
      exact hm } }

end

/-! ## Part 2 : Unique existence
  We introduce the useful `∃!` notation. Given a type `α` and `p : α → Prop`, `∃! x : α, p x` is
  a proposition asserting that there exists a unique term `x : α` such that `p x` holds.
  This is equivalent to `∃ x, p x ∧ ∀ y, p y → y = x`.
-/

-- Examine the following example to see how `∃!` is defined; then try to prove it.
example : ∃! x : ℕ, x = 0 := ⟨_, ⟨rfl, λ _ h => h⟩⟩

-- more generally (with the same exact proof as above):
example {α : Type} (a : α) : ∃! b, b = a := ⟨_, ⟨rfl, λ _ h => h⟩⟩


-- The `∃!` notation can take several variables, but this can be quite confusing.
-- For example, try to understand what the following lemma is saying, and then prove it.
lemma Nat.exists_unique_le : ∃! n m : Nat, m ≤ n :=
⟨0, ⟨0, ⟨le_rfl, λ _  h => eq_zero_of_le_zero h⟩⟩,
  λ y ⟨_, _, hmm⟩ => by rw [hmm y le_rfl, hmm _ (Nat.zero_le _)]⟩

/-! ## Part 3 : Types and logic
  Here we examine some interesting interactions between types and logic.
-/

-- Lean has an inductive type (class) called `Nonempty`. It represents when a type has at least
-- one term. You can `ctrl/cmd + click` on `Nonempty` to see its definition.
#check Nonempty

-- Given that it is an inductive type, do you see how you could use and construct a term of
-- type `Nonempty α` for some type `α`? Try the following:

example : Nonempty ℕ := ⟨0⟩

example {α β : Type} : Nonempty α → Nonempty β → Nonempty (α × β) := λ hα hβ => ⟨hα.some, hβ.some⟩


-- Now try to understand and prove the following lemma.
theorem existence_implies_everything_iff {α : Type*} (r : α → Prop) :
  (∃ x, (r x → ∀ y, r y)) ↔ Nonempty α :=
⟨λ ⟨x, _⟩ => Nonempty.intro x, λ _ => forall_imp_iff_exists_imp.mp fun a y => a y⟩

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
  (p : Type → Prop) (hα : p α) (hβ : ¬ p β) : α ≠ β := by
rintro rfl; contradiction

-- Now prove that there exists two types that are not equal.
theorem exists_ne_types : ∃ α β : Type, α ≠ β :=
⟨ℕ, Empty, λ h => by cases h.mp 1⟩

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

variable {α : Type} in
#check #α
-- This is the same as `Quotient.mk Cardinal.isEquivalent α`.

-- Now prove that two types where one is countable and one isn't cannot be equal.
lemma ne_types_of_countable_uncountable {α β : Type}
  (hα : Countable α) (hβ : Uncountable β) : α ≠ β :=
ne_types_of_different_property _ hα ((uncountable_iff_not_countable _).mp hβ)

-- Now prove this. (Hint: you don't need to use the previous one.)
lemma ne_types_of_ne_cardinal {α β : Type} (h : #α ≠ #β) : α ≠ β :=
by { rintro rfl; contradiction }

-- *Reminder*: if you couldn't find two types that were not equal before, go back to theorem `exists_ne_types` a try it now.

end


/-! ## Part 5 : Nat.cast is not surjective
  For this last question, we will prove that the obvious inclusion `ℕ → ℤ` is not surjective.
  In Lean, this inclusion is called `Nat.cast`.
-/

open Function

#check (Nat.cast : ℕ → _)
-- Cast is defined in greater generality as a function `ℕ → α` for certain types `α`.
-- This argument is implicit, but we can provide it explicilty using the `(α := ℤ)` syntax.
#check Nat.cast 0
-- Note that Lean uses the `↑` notation for `Nat.cast`. We will learn more about this next week.

lemma not_surjective_nat_int : ¬ Surjective (Nat.cast : ℕ → ℤ) := λ h => by
{ obtain ⟨x, hx⟩ := h (-1)
  simp only [Int.reduceNeg] at hx }

-- You may find the following lemma(s) useful.
#check Nat.cast_le (α := ℤ)
#check Nat.cast_nonneg (α := ℤ)
