/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
 # Week 7 - Diamonds

 In this file, we will learn how to identify and resolve diamonds (type mismatch errors).

 **Diamonds** are when we have the following type inheritance diagram:
    D
   / \
  B   C
   \ /
    A
  i.e., a diamond is when we have `D` being inferred by both `B` and `C` which are inferred by `A`.

 We call a diamond **transparent** when `D` (inferred by `B`) is definitionally equal to
  `D` (inferred by `C`). We also sometimes say that a diamond is "resolved" when there are no
  non-transparent sub-diamonds (i.e., diamonds within the diamond). In other words, when the error
  is resolved.
-/

section type_inheritance_diagram_example

/-
 type `A` with instance `B : Ring A` and `C : AddCommGroup A` means we have the following type inheritance diagram:

  B   C
   \ /
    A
-/
variable {A : Type} [B : Ring A] [C : AddCommGroup A]

-- now let `D` be `AddCommMonoid A`, and we know that this is inferred by `B` and `C`:
#check B.toAddCommMonoid
#check C.toAddCommMonoid

/-
 so then we have a diamond inheritance:
    D
   / \
  B   C
   \ /
    A
-/

end type_inheritance_diagram_example

/- `NormedAddCommGroup`, `InnerProductSpace`, `Ring`, `Algebra` and `Finite_dimensional`
  gives a mismatch error when trying to deal with linear maps. -/
-- example {E : Type*} [hE₁ : NormedAddCommGroup E] [hE₂ : InnerProductSpace ℂ E]
--   [hE₃ : Ring E] [hE₄ : Algebra ℂ E] (T : E →ₗ[ℂ] E) [hE₅ : FiniteDimensional ℂ E] :
--   LinearMap.adjoint T = T :=
-- sorry

section naive_approach

/-!
 ## Fixing the error: the naive approach
-/

-- can we be more specific to fix the error?
-- example {E : Type*} [hE₁ : NormedAddCommGroup E] [hE₂ : InnerProductSpace ℂ E]
--   [hE₃ : Ring E] [hE₄ : Algebra ℂ E] (T : E →ₗ[ℂ] E) [hE₅ : FiniteDimensional ℂ E] :
--   @LinearMap.adjoint ℂ E E Complex.instIsROrCComplex hE₁ hE₁ hE₂ hE₂ hE₅ hE₅ T = T :=
-- sorry

/- nope
  ... so how do we fix this?!

  according to the Infoview,
  there seems to be two "non-transparent diamonds".
  the first `◇` is `AddCommGroup.toAddCommMonoid` clashing with
  `NonUnitalNonAssocSemiring.toAddCommMonoid`
  this is because the following are not definitionally equal: -/
-- example {E : Type*} [hE : NormedAddCommGroup E] [hE₂ : Ring E] :
--   hE.toAddCommMonoid = hE₂.toAddCommMonoid :=
-- rfl -- gives an error

-- can we specify which instances the linear map should access?
-- example {E : Type*} [hE₁ : NormedAddCommGroup E] [hE₂ : InnerProductSpace ℂ E]
--   [hE₃ : Ring E] [hE₄ : Algebra ℂ E] (T : E →ₗ[ℂ] E) [hE₅ : FiniteDimensional ℂ E] :
--   LinearMap.adjoint (T : @LinearMap ℂ ℂ _ _ _ E E
--     (hE₁.toAddCommMonoid) (hE₁.toAddCommMonoid)
--     (NormedSpace.toModule) (NormedSpace.toModule)) = T := sorry

-- nope...
-- can we fix this by reordering the instances?
example {E : Type*} [hE₁ : NormedAddCommGroup E] [hE₂ : InnerProductSpace ℂ E]
  (T : E →ₗ[ℂ] E) [Ring E] [Algebra ℂ E] [hE : FiniteDimensional ℂ E] :
  LinearMap.adjoint T = T := sorry

-- yes!

-- BUT, what if we needed to define a linear map in the proof?
example {E : Type*} [hE₁ : NormedAddCommGroup E] [hE₂ : InnerProductSpace ℂ E]
  (T : E →ₗ[ℂ] E) [Ring E] [Algebra ℂ E] [hE : FiniteDimensional ℂ E] :
  LinearMap.adjoint T = T := by
{
  -- let f : E →ₗ[ℂ] E := sorry
  -- have : @LinearMap.adjoint ℂ E E _ hE₁ hE₁ hE₂ hE₂ hE hE f = 0 := sorry
  -- back to the error...

  -- one way to fix this is by specifying the function:
  let f' : @LinearMap ℂ ℂ _ _ (RingHom.id ℂ) E E (NormedAddCommGroup.toAddCommGroup.toAddCommMonoid)
    (NormedAddCommGroup.toAddCommGroup.toAddCommMonoid)
    (NormedSpace.toModule) (NormedSpace.toModule) := sorry
  have this' : LinearMap.adjoint f' = 0 := sorry

  -- this works fine BUT there must be a better way to handle this error than to do this
  -- every time??

  sorry
}

end naive_approach

section resolving_diamonds

/-!
 ## Resolving diamonds
-/

/-
 We already concluded previously that there are non-transparent diamonds within our example.

 The first is `NormedAddCommGroup` clashing with `Ring`.
-/

/- note that we have the following transparent diamond `◇`,
  i.e., `AddCommMonoid` created by `Ring → AddCommGroup` is definitionally equal to that
  created by `Ring → NonUnitalNonAssocSemiring → AddCommMonoid`. -/
example {E : Type*} [h : Ring E] :
  ((h.toAddCommGroup).toAddCommMonoid : AddCommMonoid E) = h.toAddCommMonoid :=
rfl

/-- `NormedAddCommGroup` structure with `Ring`, i.e., the properties of `Ring`
  and `NormedAddCommGroup`, but without the common property `AddCommGroup`. -/
@[class, reducible] structure NormedAddCommGroup_ofRing (E : Type*)
  extends Norm E, Ring E, MetricSpace E where
  dist := fun x y => ‖x - y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x - y‖ := by aesop

instance NormedAddCommGroup_ofRing.inst_Ring {E : Type*} [h : NormedAddCommGroup_ofRing E] :
  Ring E :=
h.toRing
instance NormedAddCommGroup_ofRing.inst_NormedAddCommGroup {E : Type*}
  [h : NormedAddCommGroup_ofRing E] :
  NormedAddCommGroup E :=
{ toNorm := h.toNorm
  toAddCommGroup := h.toAddCommGroup
  toMetricSpace := h.toMetricSpace
  dist_eq := h.dist_eq }

/-
 Let's check that we now get the same `AddCommMonoid`:
-/
example {E : Type*} [h : NormedAddCommGroup_ofRing E] :
  h.toAddCommMonoid = NormedAddCommGroup.toAddCommGroup.toAddCommMonoid :=
rfl

/-
 We also get the same `AddCommGroup` structure:
-/
example {E : Type*} [NormedAddCommGroup_ofRing E] :
  (NormedAddCommGroup.toAddCommGroup : AddCommGroup E) = Ring.toAddCommGroup :=
rfl

/- we have resolved the first diamond! -/

-- this now works!!!
example {E : Type*} [hE₁ : NormedAddCommGroup_ofRing E] [hE₂ : InnerProductSpace ℂ E]
  [Algebra ℂ E] [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) :
  LinearMap.adjoint T = 0 := by
{
  let f : E →ₗ[ℂ] E := sorry
  have : LinearMap.adjoint f = T := sorry
  sorry
}

-- but we still have some issues remaining to address:
-- example {E : Type*} [hE₁ : NormedAddCommGroup_ofRing E] [hE₂ : InnerProductSpace ℂ E]
--   [hE₃ : Algebra ℂ E] [hE₄ : FiniteDimensional ℂ E]
--   (T : E →ₗ[ℂ] E) (x y : E) :
--   ⟪T (x * y), T x⟫_ℂ = (LinearMap.adjoint (Algebra.linearMap ℂ E)) x := sorry

/- The error is because of the following non-transparent diamond:
  the module (inferred by the inner product space) is not definitionally equal to that
  inferred by the algebra. -/
-- example {E : Type*} [NormedAddCommGroup_ofRing E]
--   [h : InnerProductSpace ℂ E] [Algebra ℂ E] :
--   h.toModule = Algebra.toModule :=
-- rfl

/--
 `Algebra ℂ A` instance given `A` as a Semiring, `ℂ` Module, and
 has `SMulCommClass ℂ A A` and `IsScalarTower ℂ A A`
 (see implementation notes `Mathlib.Algebra.Algebra.Basic#implementation_notes`)
-/
instance {R A : Type*} [CommSemiring R] [Semiring A]
  [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] : Algebra R A :=
Algebra.ofModule smul_mul_assoc mul_smul_comm

/-
 Now the module given by the inner product space **is** definitionally equal to that
   inferred by the algebra (which is given by the module of the inner product space).
-/
example {E : Type*} [NormedAddCommGroup_ofRing E]
  [h : InnerProductSpace ℂ E] [SMulCommClass ℂ E E]
  [IsScalarTower ℂ E E] :
  h.toModule = Algebra.toModule :=
rfl

/- we have resolved all our diamonds! -/

-- ay this works now!!! 🎉
example {E : Type*} [hE₁ : NormedAddCommGroup_ofRing E] [hE₂ : InnerProductSpace ℂ E]
  [SMulCommClass ℂ E E] [IsScalarTower ℂ E E] [FiniteDimensional ℂ E]
  (T : E →ₗ[ℂ] E) (x y : E) :
  ⟪LinearMap.adjoint T (x * y), T x⟫_ℂ = (LinearMap.adjoint (Algebra.linearMap ℂ E)) x := sorry

end resolving_diamonds
