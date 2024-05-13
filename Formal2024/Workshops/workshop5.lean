/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Library
import Mathlib.GroupTheory.Coset

/-!
  # Inductive types, subtypes and quotient types
  References: [MIL] Mathematics in Lean, [Tut] Tutorials project.
  This week we will also use the textbook [TPL] Theorem Proving in Lean 4, which can
  be found at https://leanprover.github.io/theorem_proving_in_lean4/
-/

/-
  In the type theory of Lean (a version of the Calculus of Inductive Constructions),
  there are only a few types that whose existence is axiomatic. These are:
  - The type universes `Prop`, `Type`, `Type 1`, `Type 2`, ...
  - The (dependent) function type `(x : α) → β x` for `α : Type*` and `β : α → Type*`.

  (Almost) every other type is built up from these and the construction of inductive types.
  This includes the familiar `∧`, `∨`, `∃`, and `↔` types.
-/

section

-- Before me dive into inductive types. Let's revisit those two basic types we just mentioned.
-- We have the hierarchy of type universes indexed by the natural numbers:
#check Type 0 -- = Type
#check Type 1
#check Type 2
-- These can can also be written as `Sort 1` (= `Type 0`), `Sort 2` (= `Type 1`), etc.
-- In this notation `Sort 0` is the same as `Prop`.
#check Sort 0
#check Sort 1

-- `Prop` is a rather special type. A term of type `Prop` is a proposition `p : Prop`, which
-- we think of as being either true or false. Any two terms of type `p` are considered
-- definitionally equal by Lean. This is the aximo of *proof irrelevance*.
example {p : Prop} (h1 h2 : p) : h1 = h2 := rfl

-- The function type also deserves some more attention. Lean is what is called a dependently
-- typed language, which means that it allows for *dependent functions*. These are functions
-- where the type of the output can depend on the value of the input.

-- This is a normal function
#check fun (n : ℕ) => n + 1
-- This is a dependent function
#check fun (n : ℕ) => Vector.replicate n (1 : ℝ)

-- We've been using dependent functions all this time without noticing! For example, every
-- time we write a `∀` statement, we are writing a dependent function type.
#check ∀ (n : ℕ), 0 ≤ n

end

section

/-
  # Inductive types

  An inductive type is a type defined by a list of constructors.
  For example, we could define our own version of the `Bool` type.
-/
inductive MyBool where
  | false : MyBool
  | true : MyBool

-- This will create a type `MyBool` with two constructors `MyBool.false` and `MyBool.true`.
#check MyBool
#check MyBool.false
#check MyBool.true

-- Lean also creates a convenient namespace for the type and its constructors.
namespace MyBool

-- Inside the namespace, the constructor names are shorter:
#check false
#check true

-- To use this type, we can use *pattern matching*. (Pay attention to the syntax!)
def and : MyBool → MyBool → MyBool
  | true, true => true
  | _, _ => false

-- We can also use tactics like `rcases` and `rintro`:
def and' : MyBool → MyBool → MyBool := by
  rintro (true | false) (true | false)
  · exact true
  repeat { exact false }

end MyBool
end

section

#check Nat.add

-- The constructors of an inductive types can also take arguments, even of the type being
-- defined. This is the case for one of the most important types:
inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat

-- You can read this as: a natural number is either `zero` or the successor of another
-- natural number.

namespace MyNat

-- Here is how addition is defined in Lean.
def add : MyNat → MyNat → MyNat
  | n, zero => n
  | n, succ m => succ (add n m)
-- Note that this definition is recursive! However, Lean is able to tell that this recursion
-- is well-founded, i.e. it will always terminate. This is thanks to the theory of inductive
-- types, which Lean is aware of.

lemma add_zero (n : MyNat) : add n zero = n := rfl
lemma add_succ (n m : MyNat) : add n (succ m) = succ (add n m) := rfl

-- Using pattern matching or `racses`/`rintro` is not always enough to prove things about
-- inductive types. Sometimes we need to use *induction*.
lemma zero_add (n : MyNat) : add zero n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [add_succ, ih]

-- There is also the `induction'` tactic, which is more powerful (see `generalizing`) and
-- makes the different cases less explicit.
lemma zero_add' (n : MyNat) : add zero n = n := by
  induction' n with n ih
  · rfl
  · rw [add_succ, ih]

-- What happens if instead of `induction'` we use `rcases`?

-- Lean is able to do induction on any inductive type. Every time we define an inductive type,
-- Lean generates some induction principles for us. These are called `rec` and `recOn`, and they
-- are what the `induction` tactic uses under the hood.
#check MyNat.rec
-- MyNat.rec.{u}
--   {motive : MyNat → Sort u}
--   (zero : motive zero)
--   (succ : (n : MyNat) → motive n → motive (succ n))
--   (t : MyNat)
-- : motive t
#check MyNat.recOn

/-
  # Exercises
-/

-- 1. Prove that addition is associative. (Can you do it in 3 lines?)

lemma add_assoc (n m k : MyNat) : add (add n m) k = add n (add m k) := by
  sorry

-- Hint: we defined what `add n (succ m)`, with the successor on the right.
-- Does it help to induct on the rightmost argument?

-- 2. Define multiplication in terms of addition.

def mul : MyNat → MyNat → MyNat
  | n, zero => zero
  | n, succ m => sorry

lemma mul_zero (n : MyNat) : mul n zero = zero := rfl
lemma mul_succ (n m : MyNat) : mul n (succ m) = add (mul n m) n := sorry

-- Now prove that multiplying by zero on the left gives zero.

lemma zero_mul (n : MyNat) : mul zero n = zero := by
  sorry

end MyNat
end

section

-- The constructors of an inductive type can take more than one argument.
inductive MyExists {α : Type} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : MyExists p

example : MyExists (fun x : ℕ ↦ x > 0) := MyExists.intro 1 (by norm_num)

-- When we have a inductive type with only one constructor, we can use the *anonymous constructor*.
example : MyExists (fun x : ℕ ↦ x > 0) := ⟨1, by norm_num⟩

example (h : MyExists (fun x : ℕ ↦ x < 0)) : False := by
  rcases h with ⟨n, hn⟩
  norm_num at hn

-- Inductive types with only one constructor are called *structures*. We will learn more
-- about these next week. For now, we will just see how the syntax for defining them is a little
-- different. For example, we could have equivalently defined `MyExists` as
structure MyExists' {α : Type} (p : α → Prop) where
  w : α
  h : p w

-- If you are curious, you can `ctrl/cmd + click` on these to see how they are defined in Lean as
-- inductive types/structures.
#check And
#check Or
#check Exists
#check Iff
#check ℕ
#check ℤ
#check Prod
#check Unit
#check Empty

/-
  # Exercises
-/

-- 3. Prove that the negation of `MyExists` is what you'd expect.
example {α : Type} (p : α → Prop) : ¬ MyExists p ↔ ∀ x, ¬ p x := by
  sorry

end

-- In mathlib, some types are provided with more than just one induction principle. For example,
-- for `ℕ` we have things like
#check Nat.strong_induction_on
#check Nat.case_strong_induction_on
#check Nat.le_induction
#check Nat.subInduction
#check Nat.mod.inductionOn

-- To use these, we give the `induction'` tactic a principle to use,
-- e.g. `using Nat.strong_induction_on`.
lemma exists_prime_factor {n : ℕ} (ge2 : 2 ≤ n) : ∃ p, Nat.Prime p ∧ p ∣ n := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases hn : Nat.Prime n
  · use n, hn
  · rcases Nat.exists_dvd_of_not_prime2 ge2 hn with ⟨m, mdvdn, mge2, mltn⟩
    rcases ih m mltn mge2 with ⟨p, hp, pdvdm⟩
    use p, hp
    exact Nat.dvd_trans pdvdm mdvdn

section

/-
  # Subtypes

  Subtypes are Lean's way of dealing with subsets of a type as types themselves.
  This is very useful, since functions in Lean are defined between types, not sets.
-/

-- Subtype takes a type `α` and a predicate `p : α → Prop` on that type, and returns a new type
-- whose terms are a term `a` of `α` and a proof of `p a`. (How does this relate to `∃`?)
#check Subtype
#check Subtype (fun n : ℕ => n > 0)

-- Actually, `Subtype` itself is just an inductive type.
-- Can you guess how it is defined? (Or `ctrl/cmd + click` your way through!)

-- Lean has a convenient notation for subtypes. For example, this is the same subtype as that
-- previous one:
#check { n : ℕ // n > 0 }
-- These are just regular forward slashes `/` on your keyboard.
-- In mathlib, this type is called `ℕ+`.

-- Terms of a subtype have convenient projections.
variable (n : ℕ+)
#check n.val
#check n.prop
-- The notation `↑n` shown in the Infoview is Lean's visually less intrusive way of saying `n.val`.
-- This `↑` is called a coercion, about which we will learn more next week.

/-
  # Exercises
-/

-- 4. Define the subtype of even natural numbers.

def NatEven : Type := sorry

-- Now define a function from `ℕ → NatEven` that takes a natural number `n` and returns `2 * n`.

def double (n : ℕ) : NatEven := sorry

end

section

/-
  # Quotient types

  Quotient types are Lean's way of dealing with types of equivalence classes under some relation.
  These are one of the few types that are not defined in terms of inductive types. Instead, they
  are an axiom of Lean's type theory.
-/

-- In Lean, equivalence relations are called `Equivalence`s. This is a structure that packages a
-- relation on a type, and a proof that it is an equivalence relation.
#check Equivalence

-- A type equipped with an equivalence relation is a `Setoid`. This is defined as a `class` which
-- is a particular kind of structure. We will learn more about classes next week.
#check Setoid

-- For example, here is a `Setoid`:
variable (n : ℕ)

def NatModRel : Setoid ℕ where
  r := fun a b => a % n = b % n
  iseqv := ⟨fun x => rfl,
    fun hxy => hxy.symm,
    fun hxy hyz => by rw [hxy, hyz]⟩
-- This is some convenient syntax for constructing structures. We will see more about it next week.
-- We provide a relation `r` and a proof that it is an equivalence relation `iseqv`.

-- The type of equivalence classes of a `Setoid` is constructed using `Quotient`.
def NatMod : Type := Quotient (NatModRel n)

-- To produce an element of a quotient, we use `mk` or `⟦⟧`.
#check Quotient.mk (NatModRel n)
#check (⟦0⟧ : NatMod n)

-- To define a function out of a quotient type, we use the universal property.
-- This can be accessed with `Quotient.lift`.
#check Quotient.lift

-- `Quotient.sound` is useful for showing that two terms of the quotient are equal.
#check Quotient.sound

-- For example, we can define a sucessor function on `ℕmod n`.
def modSucc {n : ℕ} : NatMod n → NatMod n:=
  Quotient.lift (λ k ↦ ⟦k + 1⟧) (by
    intro a b h
    apply Quot.sound
    dsimp [NatModRel]
    rw [Nat.add_mod a, Nat.add_mod b, h]
  )

-- Lastly, `Quotient.ind` lets us prove things about terms in a quotient type if we
-- can prove them for any representative.
#check Quotient.ind

example : (k : NatMod n) → ∃ h, k = ⟦h⟧ := by
  apply Quotient.ind
  intro h
  exact ⟨h, rfl⟩

-- This is a bit like an induction proof, so we can use the `induction'` tactic.
-- This is one of the reasons `induction'` is more powerful than `induction`.
example (k : NatMod n) : ∃ h, k = ⟦h⟧ := by
  induction' k using Quotient.ind with h
  exact ⟨h, rfl⟩
-- Here we are telling `induction'` that the principle of induction we want to use
-- is `Quotient.ind`.

/-
  # Exercises
-/

-- 5. Check the following property of `modSucc`.

-- You might want to use the following.
#check Quotient.lift_mk
#check Quot.sound
#check Nat.sub_add_cancel

example (hn : n ≥ 1) : modSucc (⟦n - 1⟧ : NatMod n) = ⟦0⟧ := by
  letI := NatModRel n
  -- This line will make `Quotient.lift_mk` work. You can ignore it for now. We will see more
  -- about it next week when we talk about typeclasses.
  apply Quot.sound
  dsimp [NatModRel]

-- If you are stuck with a goal of the form `a ≈ b`, try `dsimp [(· ≈ ·), NatModRel]`.
-- If you are stuck with a goal of the form `Setoid.r a b`, try `dsimp [NatModRel]`.
-- These will unfold the relevant definition to give you something more familiar looking.

end

section

-- 6. Here are two inductively defined predicates on natural numbers.

inductive even : ℕ → Prop where
  | zero : even 0
  | add_two {n : ℕ} (h : even n) : even (n + 2)

inductive odd : ℕ → Prop where
  | one : odd 1
  | add_two {n : ℕ} (h : odd n) : odd (n + 2)

-- Prove the following three lemmas.

-- If you get stuck, remember that `even` and `odd` are inductive types, so they come with their
-- own recursion principle.
#check even.rec
#check odd.rec

lemma odd_of_succ_even (n : ℕ) : even n → odd (n + 1) := by
  sorry

lemma even_of_succ_odd (n : ℕ) : even n → odd (n + 1) := by
  sorry

lemma even_or_odd (n : ℕ) : even n ∨ odd n := by
  sorry

-- If you would like some more practice, come up with your own lemmas about how `even` and `odd`
-- interact with other operations on the natural numbers. For example, you could prove that the sum
-- of two even numbers is even, or that the sum of an even and an odd number is odd.

end
