/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Library

/-!
# Homework 6: Structures and Classes
References: [MIL] Mathematics in Lean.
-/

/-!
# Problem 1: Structures [MIL 6.1]
Here we define the structure of a standard simplex and ask you to prove something about it.
-/

/-
The standard 2-simplex is defined to be the set of points (x, y, z) satisfying x ≥ 0, y ≥ 0, z ≥ 0,
and x + y + z = 1. If you are not familiar with the notion, you should draw a picture,
and convince yourself that this set is the equilateral triangle in three-space with vertices
(1, 0, 0), (0, 1, 0), and (0, 0, 1), together with its interior.
-/

structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1

namespace StandardTwoSimplex

-- The below will use division of real numbers, so we open a `noncomputable section`.

noncomputable section

-- We can define the midpoint of two points in the standard simplex,
-- and it will still be in the standard simplex.
def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := div_nonneg (add_nonneg a.x_nonneg b.x_nonneg) (by norm_num)
  y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num)
  z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num)
  sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]

-- Given a parameter λ satisfying 0 ≤ λ ≤ 1, we can take the weighted average λa + (1 - λ)b of
-- two points a and b in the standard simplex. We challenge you to define that function,
-- in analogy to the midpoint function above.

def weightedAverage (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
  (a b : StandardTwoSimplex) : StandardTwoSimplex where
  x := lambda * a.x + (1 - lambda) * b.x
  y := lambda * a.y + (1 - lambda) * b.y
  z := lambda * a.z + (1 - lambda) * b.z
  x_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.x_nonneg)
    (mul_nonneg (sub_nonneg.mpr lambda_le) b.x_nonneg)
  y_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.y_nonneg)
    (mul_nonneg (sub_nonneg.mpr lambda_le) b.y_nonneg)
  z_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.z_nonneg)
    (mul_nonneg (sub_nonneg.mpr lambda_le) b.z_nonneg)
  sum_eq := by nlinarith [a.sum_eq, b.sum_eq]

end -- end the `noncomputable section`

end StandardTwoSimplex

/-!
# Problem 2: Classes [MIL 7.3]
In this problem we will combine classes with what we learned about quotient types.
Our goal is to prove that the quotient of a commutative monoid by a submonoid is again a monoid.
-/

variable (M N : Type*)

#check CommMonoid
#check Submonoid
#check Submonoid.one_mem
#check Submonoid.mul_mem

-- We will define the monoid structure on the quotient type. To take the quotient type,
-- we first need a setoid. Try to fill in the following definition.
def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x * w = y * z
  iseqv := {
    refl := fun _ ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨a, ha, b, hb, h⟩ ↦ ⟨b, hb, a, ha, h.symm⟩
    trans := by
      rintro a b c ⟨w, hw, z, hz, h⟩ ⟨w', hw', z', hz', h'⟩
      refine ⟨w*w', N.mul_mem hw hw', z*z', N.mul_mem hz hz', ?_⟩
      simp_rw [mul_comm z z', ← mul_assoc, ← h', h, mul_assoc, mul_comm] }
-- Above we saw the `refine` tactic, which is like `exact` but where we can leave a gap to be
-- filled in as a new goal.

-- We register the pair (M, N) where M is a submonoid of M as an instance of the HasQuotient class,
-- allowing us to use the notation M ⧸ N for the quotient
-- (the quotient symbol is not a normal forward slash and is typed as `\quot`)
instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

-- Now we can define the monoid structure on the quotient type.
-- Try to fill in the following instance declaration.

-- You can use `Setoid.refl` but it won't always be able to detect the relvant setoid structure.
-- In that case, you can use `@Setoid.refl M N.Setoid` to explicitly specify the setoid structure.
instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) :=
  letI : Setoid M := Submonoid.Setoid M N
  -- `letI` is a shorthand for `let Instance`, which is used to declare a local instance
  { mul := Quotient.map₂' (· * ·) (λ a b ⟨c, hc, d, hd, hcd⟩ e f ⟨g, hg, h, hh, hgh⟩ ↦ by
    { refine ⟨c * g, mul_mem hc hg, d * h, mul_mem hd hh, ?_⟩
      rw [mul_assoc, mul_comm c g, ← mul_assoc e, hgh, mul_comm (f * h), ← mul_assoc, hcd,
        mul_mul_mul_comm b d f h] })
    mul_assoc := by
    { rintro ⟨_⟩ ⟨_⟩ ⟨_⟩
      exact Quotient.sound (by simp_rw [mul_assoc]; rfl) }
    one := QuotientMonoid.mk M N 1
    one_mul := by
      rintro ⟨a⟩
      exact Quotient.sound (by simp_rw [one_mul]; rfl)
    mul_one := by
      rintro ⟨a⟩
      exact Quotient.sound (by simp_rw [mul_one]; rfl) }
