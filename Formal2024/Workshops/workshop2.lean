/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Mathlib.Data.Real.Basic
import Library

/-!
  # Logic: Implication, universal quantifier, existential quantifier, negation
  References: [MIL] Mathematics in Lean, [Tut] Tutorials project.
  Most of the demonstration section comes [MIL].
-/

namespace Week2


/-!
  # Implication and universal quantifier
-/

-- To write `∀` type `\forall`

-- Lean treats the universal quantifier as an implication
-- Implications are grouped on the RIGHT (N.B. this is different from the usual convention for operations like +, *, ...)

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

-- Lean is all about types, and checking that something is of the right type
section
-- Naively, you can think of types as sets. Here these variables are real numbers
variable (a b δ : ℝ)

-- Lean has a special type for propositions, called `Prop`
#check a+b=δ

-- Lean doesn't care if a Proposition is true or false, as long as it is well-formed
#check 2+2=5
#check 1=1
-- #check == -- Delete this line to get rid of the error message

-- Being of the type of a Proposition means being a proof
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)


-- An implication is like a function from sets of proofs to set of proofs
#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

-- Notice the syntax: if `f` is a function, Lean reads `f x` as `f(x)` (and gives error if `x` is not a valid input)
-- Lean automatically groups on the left, so `f x y` means `f(x)(y)`
-- If you need a different order you need to specify it with appropriate brackets

-- Notice that throughout this section, defined using `section` and `end`, everything defined with `variable` was always visible in the context. Outside of the section these variables will not be available in the context.
end


-- To prove an implication statement, we use `intro`

example: ∀ x y z : ℝ, x ≤ y → y ≤ z → x ≤ z := by
  intro x y z h₀ h₁
  -- Now we can proceed as usual
  apply le_trans
  · exact h₀
  · exact h₁

-- Lean allows named hypotheses. The two following examples are equivalent:
section

variable (P Q : Prop)

theorem ex1 : P → Q := by sorry

theorem ex2 (h : P) : Q := by sorry

#check ex1
#check ex2

-- Lean allows for implicit arguments, using the curly brackets,
-- when it is possible to infer them from context:

theorem ex3 {n : ℕ} (hyp : n > 1) : n + 1 > 0 := by sorry

variable (a : ℕ)
variable (ha : a > 1)

#check ex3 ha

-- Notice that passing the implicit argument gives an error.
-- To pass an implicit argument you need to put a `@` before

#check @ex3 a ha



end

-- Using the universal quantifier, we define an upper bounded function
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

section

variable (f g : ℝ → ℝ) (a b : ℝ)

-- It is useful to define functions, this can be done with the command `fun`

#check fun x ↦ x + 1
#check fun x ↦ f x + g x

-- We can use implication hypothesis to get new hypotheses

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  -- This step makes Lean unpack the definition of the function.
  -- It is not needed, but it makes things clearer
  apply add_le_add
  · exact hfa x
  -- `hfa x` is now a proof of `f x ≤ a`
  · exact hgb x

/-
Since Lean sees an implication as a function from proofs of a Proposition to
proofs of another Proposition, we can write the proof term explicitly, using `fun`.
This is more concise, but probably less "human-like." Where to draw the line between
conciseness and human readability is up to you!
-/

theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x) -- Note the brackets (terms would be grouped on the left by default)




/-!
# Exercises
-/

-- Let us define the property a lower bounded function
def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x


-- 1.  Prove this using `intro`

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) :=
  sorry

-- 2. Now try proving it without using any tactic, writing a proof term

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) :=
  sorry

-- 3. Here you may need the theorem `mul_nonneg`

#check mul_nonneg

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 :=
  sorry

end



/-!
  # Existential quantifier
-/

-- To write `∃` type `\exists`.

/-!
  To prove an exists statement, we need to provide 2 things. An object of
  the correct type and a proof that it satisfies the desired property.
  The first step is done with `use`
-/

 example : ∃ x : ℝ, 2 * x = 5 := by
  use 5/2 -- Notice how the goal has changed
  norm_num -- This is a useful tactic that does arithmetic computations.

-- We can construct a proof term explicitly using the "anonymous constructor" notation.
-- For this we give the element with the desired property, followed by a proof of the property,
-- inside angle brackets `⟨⟩` (you can type these using `\<>`).

example : ∃ x : ℝ, 2 * x = 5 :=
  ⟨5/2 , by norm_num⟩ -- Lean matches the given data with the goal

-- To use an exists statement, we need the command `rcases` and the anonymous constructor

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a -- `f` has an upper bound

example (f g) (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  -- Adds new variable `a` (the upper bound) with property `ubfa` (`a` is the upper bound)
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add ubfa ubgb

  -- `intro` and `rcases` can be combined into one command: `rintro`

example (f g) : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩


/-!
# Exercises
-/

-- We open the `Function` namespace to be able to use theorems and definitions about functions with shorter names, e.g. `Surjective f` instead of `Function.Surjective f`.
open Function

-- 4. The definition of surjective function involves a universal and an exist quantifier.
-- `Surjective (f : ℝ → ℝ) := ∀ y, ∃ x, f x = y`
-- Prove the following using both `intro` and `use`


example {c : ℝ} : Surjective fun x ↦ x + c := by
  sorry

-- 5. Now the exist statement is given as hypothesis. Prove the goal using `rcases`
section

variable (f g : ℝ → ℝ )

example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  sorry


end
/-!
  # Negation
-/

-- To write `¬` type `\not`.
-- Lean interprets a negation `¬a` as `a → False`, so tactics for implications work


example (Q) (h : Q) : ¬¬Q := by
  intro notQ -- This creates the hypothesis `¬Q` and changes the goal to `False`
  exact notQ h
  -- We treat `¬Q` as an implication, so we can feed it a proof for `Q` to get a proof of `False`


/-!
  Lean comes with many tactics that help to deal with negation:
  · `by_contra h` applies proof by contradiction: allows us to prove `Q` by assuming
      `h = ¬Q` and changing the goal to `False`
  ⬝ `push_neg` pushes negations inside quantifiers, changing `¬∀` into `∃¬`, etc...
  ⬝ `contrapose` transforms a goal `A → B` to `¬B → ¬A`
  ⬝ `contrapose!` does `contrapose`, and then applies `push_neg` automatically
  ⬝ `exfalso` applies the theorem `False → Q`, changing the goal into `False`
-/


-- The law of excluded middle (in latin, _tertium non datur_) can only be proved by contradiction
example (Q) (h : ¬¬Q) : Q := by
  by_contra h'
  exact h h'

example (f) (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  -- We can use `push_neg` to rewrite any hypothesis, similarly to `rw`
  exact h

example (f) (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h -- `push_neg` automatically simplifies things
  exact h

example (a : ℝ) (h : 0 < 0) : a > 37 := by
  exfalso -- we have a contradiction (`0 < 0`), so we can prove anything we want! First change the goal to false.
  linarith -- Then let `linarith` make the contradiction explicit.

/-!
# Exercises
-/

-- 6. Prove this using `push_neg`.

def EvenFun (f : ℝ → ℝ) :=
 ∀ x, f (- x) = f x

example : ¬EvenFun fun x => 2 * x := by
--You will need to make the definition of `EvenFun` explicit first, you can do it by writing `unfold EvenFun`
  sorry


-- 7. Prove this using `by_contra`

example (P Q : Prop) (h : ¬Q → ¬P) : P → Q := by
  sorry


-- 8. Give a shorter proof using `contrapose`

example (P Q : Prop) (h : ¬Q → ¬P) : P → Q := by
  sorry
