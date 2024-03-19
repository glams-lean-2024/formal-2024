/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/

import Library

/-!
  # Structures, type classes, and class inference
  References: [TPIL] Theorem Proving in Lean, [MIL] Mathematics in Lean.
-/

/-!
  # Structures
-/

-- Structures are internally the same thing as inductive types with a single constructor.
-- They are convenient because they support special features, such as named fields and inheritance.

universe u v

-- Here we define an "α point" (a pair of terms of type α) as an inductive type with a single
-- constructor.
inductive Point' (α : Type u) : Type u
| mk : α → α → Point' α

-- We can do the same thing using the `structure` keyword.
@[ext]
structure Point (α : Type u) : Type u :=
mk :: (x : α) (y : α)
deriving Repr -- this line allows Lean to produce text representations in the infoview.

#check Point
#check @Point.recOn
#check @Point.mk -- `mk` is the default constructor name

-- Structures support projection onto their fields
#check @Point.x
#check @Point.y

-- Use of the `@[ext]` attribute means Lean generates theorems for proving things by extensionality
#check Point.ext

example (a b : Point ℕ ) (hx : a.x = b.x) (hy : a.y = b.y) : a = b := by
  ext
  repeat' assumption

-- We can print all the details of a structure using `#print prefix`.
#print prefix Point

-- Notice that the inductive type version has fewer supporting functions.
#print prefix Point'

-- There are various ways to define instances of a structure.
-- By providing the named fields directly:
#check { x := 10, y := 20 : Point ℕ }
#check { y := 20, x := 10 : Point ℕ }
#check ({x := 10, y := 20} : Point ℕ)

-- Using the anonymous constructor:
#check (⟨10, 20⟩ : Point ℕ)

-- Using the default constructor:
#check (Point.mk 10 20)

-- The anonymous constructor and named fields are useful for defining functions on structures.

namespace Point -- any structure creates a namespace

def add : Point ℕ → Point ℕ → Point ℕ :=
  λ a b => ⟨a.x + b.x, a.y + b.y⟩

def smul (n : ℕ) (p : Point ℕ) :=
  Point.mk (n * p.x) (n * p.y)

end Point

#check @Point.add
#check @Point.smul

def p := Point.mk 1 2
def q := Point.mk 3 4

-- Notice the order in which arguments are input to functions here.
#eval p.add q
#check p.add q

#eval p.smul 3
#check p.smul 3

-- We can extend structures by adding new fields. Here we extend a `Point` by adding RGB values.

structure RGBValue where
  red : ℕ
  green : ℕ
  blue : ℕ

structure RGBPoint (α : Type*) extends Point α, RGBValue

#print prefix RGBPoint
#check RGBPoint.mk
#check RGBPoint.toPoint
#check RGBPoint.toRGBValue
def cp := RGBPoint.mk (Point.mk 1 2) (RGBValue.mk 10 20 30)

#eval cp.x
#eval cp.red

-- We can use the fields of a structure to specify constraints that must be satisfied.

structure RedGreenPoint (α : Type*) extends Point α, RGBValue where
  no_blue : blue = 0

#check RedGreenPoint.mk

def rgp : RedGreenPoint ℕ :=
  { p with red := 200, green := 40, blue := 0, no_blue := rfl }

example : rgp.x   = 1 := rfl
example : rgp.red = 200 := rfl

-- Here is an example of the use of fields in a structure to give contraints.

structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  mul_left_inv : ∀ x : α, mul (inv x) x = one

/-!
# Exercises
-/

-- 1. Prove associativity of addition on `Point ℕ`. [MIL 6.1]

namespace Point

theorem add_assoc (a b c : Point ℕ) : (a.add b).add c = a.add (b.add c) := by
{ simp only [add, Point.ext_iff, Nat.add_assoc]
  tada }

end Point

-- 2. Here we define a type of special RGB points.

structure SpecialPoint extends Point ℕ, RGBValue where
  gradientEqn : x = red

-- Now define an addition function for special points.

namespace SpecialPoint

def add : SpecialPoint → SpecialPoint → SpecialPoint := λ a b ↦ sorry

end SpecialPoint

/-!
  # Type Classes
-/

-- To access Lean's type class system, we need to use classes rather than structures.
-- These are defined just like structures but with the `class` keyword.
-- This is just like defining a structure with the `@[class]` attribute.

class Group₂ (α : Type*) :=
  (mul: α → α → α)
  (one: α)
  (inv: α → α)
  (mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z))
  (mul_one: ∀ x : α, mul x one = x)
  (one_mul: ∀ x : α, mul x one = x)
  (mul_left_inv : ∀ x : α, mul (inv x) x = one)

#check @Group₂.mul

-- Given any term `x` where Lean knows the type `α` of `x` has a `Group₂` structure,
-- then we define the function of squaring.

def my_square {α : Type*} [Group₂ α] (x : α) := Group₂.mul x x

#check @my_square

-- Here, the square brackets denote an implicit `Group₂` structure should be inferred on `α`,
-- just like the curly brackets denote that `α` itself should be inferred from `x`.

-- For another example, let's think about the type of equivalences of a type.

section
variable (α β γ : Type*)
variable (f : α ≃ β) (g : β ≃ γ)

#check Equiv α β

#check (f.toFun : α → β)
#check (f.invFun : β → α)

#check (Equiv.refl α : α ≃ α)
#check (f.symm : β ≃ α)
#check (f.trans g : α ≃ γ)

example (x : α) : (f.trans g).toFun x = g.toFun (f.toFun x) := rfl

example (x : α) : (f.trans g) x = g (f x) := rfl

example : (f.trans g : α → γ) = g ∘ f := rfl

end

-- Here we show that the equivalences of `α` are an instance of `Group₂`

instance {α : Type*} : Group₂ (Equiv.Perm α) :=
{ mul          := λ f g ↦ Equiv.trans g f
  one          := Equiv.refl α,
  inv          := Equiv.symm,
  mul_assoc    := λ _ _ _ ↦ (Equiv.trans_assoc _ _ _),
  one_mul      := Equiv.trans_refl,
  mul_one      := Equiv.refl_trans,
  mul_left_inv := Equiv.self_trans_symm }

-- Now class inference can be performed. Below we can use that self-equivalences of β form a group
-- without having to specify the group structure, since we have already told Lean that.

section
variable {β : Type*} (f g : Equiv.Perm β)

example : Group₂.mul f g = g.trans f := rfl

example : my_square f = f.trans f := rfl

end

-- By registering instances of `Mul` etc, we can use notation

instance has_mul_Group₂ {α : Type*} [Group₂ α] : Mul α := ⟨Group₂.mul⟩

instance has_one_Group₂ {α : Type*} [Group₂ α] : One α := ⟨Group₂.one⟩

instance has_inv_Group₂ {α : Type*} [Group₂ α] : Inv α := ⟨Group₂.inv⟩

-- We could also have used the `extends` keyword to define `Group₂` extending of `Mul`, `One`,
-- and `Inv`, just like we did with structures. See Exercise 4 for an example of this.

-- Now that we have specified `Group₂` extends/is an instance of `Mul`, `One`, and `Inv`,
-- we can use the notation for these operations.

section
variable {α : Type*} (f g : Equiv.Perm α)

#check f * 1 * g⁻¹

def foo: f * 1 * g⁻¹ = g.symm.trans ((Equiv.refl α).trans f) := rfl

end

/-!
# Exercises
-/

-- 3. Modify the definition of `Point.add` so that it works for any type `α` which supports addition.

-- Hint: Try to find a suitable class in Mathlib. Whatever it is, it had better be implemented by ℕ.
-- [https://leanprover-community.github.io/mathlib-overview.html]

-- 4. Here we define a class of semigroups (a type with an associative operation on it).
-- Show that the natural numbers are a semigroup, and that the product of
-- two semigroups is a semigroup.

class MySemigroup (G : Type u) extends Mul G : Type u :=
(mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c))

namespace MySemigroup

instance NatSemigroup : MySemigroup ℕ :=
{ mul_assoc := λ _ _ _ ↦ Nat.mul_assoc _ _ _ }

instance ProdSemigroup {G : Type u} {H : Type v} [MySemigroup G] [MySemigroup H] :
  MySemigroup (G × H) :=
{ mul_assoc := λ _ _ _ ↦ Prod.ext (MySemigroup.mul_assoc _ _ _) (MySemigroup.mul_assoc _ _ _) }

end MySemigroup
