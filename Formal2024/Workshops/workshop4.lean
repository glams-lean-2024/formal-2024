/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Library
open Set

/-!
  # Sets and Functions
  References: [MIL] Mathematics in Lean, [Tut] Tutorials project.
  Most of the demonstration section comes from [MIL].
-/

section

-- Let `α` be a generic type
variable {α : Type*}

-- We denote by `Set α` the type of sets of elements of `α`
variable (s t u : Set α)
#check s

end
-- This may be confusing, as we were intuitively thinking of types as sets

/-
  # What actually is a type?
-/
section
-- Type is the primitive notion in the Calculus of Inductive Constructions, upon which Lean is based
-- Every term has a type

#check 1
#check 1+1=2 -- We discussed how `Prop` is the type of propositions

#check ℕ -- The type of `ℕ` is the type of types, called `Type`
#check Prop -- Same for `Prop`
#check Type -- Lean has a countably infinite hierarchy of type of types (of types of types...)
#check Type 1
--#check Type 33 -- Well, almost infinite
-- **Note:** However, you can manually increase the default `maxUniverseOffset`,
--   but you should not mess around with such options unless you know for sure what you're doing!
set_option maxUniverseOffset 33
#check Type 33

#check Prop → ℕ -- We can construct types of functions between types
#check Type 1 → Type 2

-- There are two inference rules that tell us that functions work like we would expect

variable {α β : Type*} -- With the asterisk we are leaving the level of the type generic
#check α
#check β
variable (f : α → β)
variable (a : α)

#check f a -- We can apply functions, getting the expected outcome

def myAnd (P : Prop) : Prop := P ∧ P

#check fun (P: Prop) ↦ myAnd P -- We can perform abstractions to create functions


-- Apart from `∀` (which we discussed is equivalent to functions) everything else is constructed
-- starting from here (mostly using Inductive Types, as we will see).
end


section
/-
  # How is a type different from a set?
-/

def setNat : Set ℕ := univ -- This is the set of all natural numbers

-- Sets come with a predicate: `∈` (`\in` or `\mem`). Its negation is `∉` (`\notin`)

#check (1 ∈ setNat) -- This is in `Prop`
#check (1 : ℕ)     -- This is not

-- `(1 : ℕ)` is a statement in type theory, but not an element in `Prop`, our model of
-- propositional logic inside type theory.

-- Another big difference: if `a : α` and `a : β`, then `α` and `β` are definitionally equal
-- To make sense of things like subsets, intersections, union, complements, we need `Set`

end

section
variable {α : Type*}
variable (s t u : Set α)

-- We write `⊆` (`\ss` or `\subseteq`) for subset, `∩` (`\i` or `\cap`) for intersection,
-- `∪` (`\u` or `\cup`) for union, and `\` (typed as `\\`) for set difference.

-- We can also use the notation `{ y | P y }`, where `P` is a predicate, for the set of
-- elements satisfying `P`

#check subset_def
#check mem_setOf
#check inter_def
#check union_def
#check mem_diff

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, inter_def, inter_def, mem_setOf]
  rw [subset_def] at h
  -- We can use `simp only` or `rw` or `simp_rw` to unfold the definitions
  -- `simp only` is a more powerful `rw`, that also works under quantifiers
  -- `simp_rw` is similar to `simp only`, but uses the lemmas in the given order
  -- Now we can proceed as usual
  rintro x ⟨xs, xu⟩
  exact ⟨h x xs, xu⟩
  tada

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  -- This is not needed though, as the anonymus constructor forces Lean to unfold the definitions
  rintro x ⟨xs, xu⟩
  exact ⟨h xs, xu⟩ -- There may be some slight differences (here we do not need to specify `x`)
  tada


example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx                      -- Subset works like an implication
  have xs : x ∈ s := hx.1         -- Intersection works like an `∧`
  have xtu : x ∈ t ∪ u := hx.2    -- Union works like an `∨`
  rcases xtu with xt | xu
  · left
    show x ∈ s ∧ x ∈ t
-- `show` is another tactic for human readability (Lean does not need it)
-- We declare the type of the goal we are going to prove.
-- It can be used to rewrite a goal to something definitionally equal.
    exact ⟨xs, xt⟩
  . right
    show x ∈ s ∧ x ∈ u
    exact ⟨xs, xu⟩
  tada

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1   -- `x ∈ s \ t` means `x ∈ s ∧ x ∉ t`
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- `x ∈ t ∨ x ∈ u`
  rcases xtu with xt | xu
  · exact xnt xt
  . exact xnu xu
  tada

-- This is quite lengthy. We can use `rintro` to shorten the proof

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction -- We often need brackets when using `rintro` on a conjunction
  tada

-- Two sets are equal when they have the same elements. This is called "extensionality"
-- You can use it by typing `ext _`
-- This is the same tactic used to prove functions are equal if they agree on all inputs
-- When we define a structure with extensionality-like property, we can mark it with `@[ext]`
-- so that Lean adds an appropriate extensionality lemma to the `ext` tactic.
-- More on this in the next lectures.


example : s ∩ t = t ∩ s := by
  ext x -- You can give the variable a name by typing it instead of `_`
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  . rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩
  tada

-- A similar statement is the theorem `Subset.antisymm`

#check Subset.antisymm

-- Membership to intersection and union can be unfolded using the following two theorems
-- (although Lean usually does not need it)

#check mem_union
#check mem_inter_iff

-- Exercises (MIL 4.1)

-- 1
example : s ∩ (s ∪ t) = s := by
  sorry

-- 2
example : s ∪ s ∩ t = s := by
  sorry

-- 3
example : s \ t ∪ t = s ∪ t := by
  sorry

-- 4
example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  sorry

-- 5
example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  sorry

end

/-
The main difference between sets and types is the predicate `∈`. In fact, in Lean a set coincides
with its `∈` predicate:

`Set α` is defined as `α → Prop`. If `s : Set α` and `a : α`, then `a ∈ s` is defined as `s a`.
The set `{ y | P y }` is defined as the function `fun y ↦ P y` and `x ∈ { y | P y }` means `P x`.
-/
--

example : 1 ∈ { x : ℕ | 0 < x } := by norm_num

-- The empty set `∅` (you get this by typing `\empty`) is the function `fun y ↦ False`
-- The universe set is the function `fun y ↦ True`

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h


example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial -- `trivial` is the name of the canonical proof of `True`

-- Exercises (MIL 4.1)

section

variable (s t : Set ℕ)

def evenSet : Set ℕ :=
  { n | Even n }

def oddSet : Set ℕ :=
  { n | ¬Even n }

#print Prime
#print Nat.Prime

-- 6
example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ oddSet := by
  sorry

-- The notation `∀ x ∈ t` means `∀ x, x ∈ t → ... `, and `∃ x ∈ t` means `∃ x, x ∈ t → ... `

-- 7
example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  sorry

-- 8
example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  sorry

end
