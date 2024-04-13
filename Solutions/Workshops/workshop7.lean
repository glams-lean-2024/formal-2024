/-
Copyright (c) 2024 TheLeanTeam. All rightPs reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
 # Week 7 - diamonds

 In this file, we will learn how to identify and resolve diamonds (type mismatch errors).

 To find the exercises in this file, search (`ctrl/cmd + F`) for `:TODO:`.
-/

section example_intro

/- `NormedAddCommGroup`, `InnerProductSpace`, `Ring`, `Algebra` and `Finite_dimensional`
  gives a mismatch error when trying to deal with linear maps. -/

example {E : Type*} [hE₁ : NormedAddCommGroup E] [hE₂ : InnerProductSpace ℂ E]
  [hE₃ : Ring E] [hE₄ : Algebra ℂ E] (T : E →ₗ[ℂ] E) [hE₅ : FiniteDimensional ℂ E]
  (h : (LinearMap.adjoint T) = T) :
  T = T :=
sorry

/-!
 ## Attempting to fix the error: the naive approach
-/

-- can we be more specific to fix the error?

example {E : Type*} [hE₁ : NormedAddCommGroup E] [hE₂ : InnerProductSpace ℂ E]
  [hE₃ : Ring E] [hE₄ : Algebra ℂ E] (T : E →ₗ[ℂ] E) [hE₅ : FiniteDimensional ℂ E]
  (h : @LinearMap.adjoint ℂ E E Complex.instIsROrCComplex hE₁ hE₁ hE₂ hE₂ hE₅ hE₅ T = 0) :
  T = 0 :=
sorry

/- nope
  ... so how do we fix this?!

  According to the Infoview,
  it seems that `AddCommGroup.toAddCommMonoid` is clashing with
  `NonUnitalNonAssocSemiring.toAddCommMonoid`.

  This is because the following are not definitionally equal: -/

example {E : Type*} [hE : NormedAddCommGroup E] [hE₂ : Ring E] :
  hE.toAddCommMonoid = hE₂.toAddCommMonoid :=
rfl -- gives an error

-- can we specify which instances the linear map should access?

example {E : Type*} [hE₁ : NormedAddCommGroup E] [hE₂ : InnerProductSpace ℂ E]
  [hE₃ : Ring E] [hE₄ : Algebra ℂ E] (T : E →ₗ[ℂ] E) [hE₅ : FiniteDimensional ℂ E] :
  LinearMap.adjoint (T : @LinearMap ℂ ℂ _ _ _ E E
    (hE₁.toAddCommMonoid) (hE₁.toAddCommMonoid)
    (NormedSpace.toModule) (NormedSpace.toModule)) = T := sorry

-- nope...
-- maybe we can we fix this by reordering the instances??
example {E : Type*} [hE₁ : NormedAddCommGroup E] [hE₂ : InnerProductSpace ℂ E]
  (T : E →ₗ[ℂ] E) [Ring E] [Algebra ℂ E] [hE : FiniteDimensional ℂ E] :
  LinearMap.adjoint T = T := sorry
-- yes!

-- BUT, what if we needed to define a linear map within the proof?
example {E : Type*} [hE₁ : NormedAddCommGroup E] [hE₂ : InnerProductSpace ℂ E]
  (T : E →ₗ[ℂ] E) [Ring E] [Algebra ℂ E] [hE : FiniteDimensional ℂ E]
  (h : LinearMap.adjoint T = T) : T = 0 := by
{
  let f : E →ₗ[ℂ] E := sorry
  have : @LinearMap.adjoint ℂ E E _ hE₁ hE₁ hE₂ hE₂ hE hE f = 0 := sorry

  -- back to the error...

  -- one way to fix this is by specifying the function:
  let f' : @LinearMap ℂ ℂ _ _ (RingHom.id ℂ) E E (NormedAddCommGroup.toAddCommGroup.toAddCommMonoid)
    (NormedAddCommGroup.toAddCommGroup.toAddCommMonoid)
    (NormedSpace.toModule) (NormedSpace.toModule) := sorry
  have this' : LinearMap.adjoint f' = 0 := sorry

  -- not very practical, but it did get rid of the above error...
  sorry
}

-- unless you resolve the diamond problem, you will always get an error if you try to access
-- both the algebra and inner product space at the same time:

example (E : Type) [hE₁ : NormedAddCommGroup E] [hE₂ : InnerProductSpace ℂ E]
  (T : E →ₗ[ℂ] ℂ) [Ring E] [Algebra ℂ E] [hE : FiniteDimensional ℂ E] :
  LinearMap.adjoint (Algebra.linearMap ℂ E) = T :=
sorry

-- so we need to learn how to resolve the diamonds in order to move on
end example_intro

section diamonds

/-
 type `A` with instance `B : Ring A` and `C : AddCommGroup A` means we have the following type inheritance diagram:

  B   C
   \ /
    A
-/

/-
 **Diamonds** are when we have the following type inheritance diagram:
    D
   / \
  B   C
   \ /
    A
  i.e., a diamond is when we have `D` being inferred by both `B` and `C` which are inferred by `A`.

 We call a diamond **transparent** when `D` (inferred by `B`) is definitionally equal to
  `D` (inferred by `C`). We also sometimes say that a diamond is **resolved** when there are no
  non-transparent sub-diamonds (i.e., diamonds within the diamond). In other words, when the error
  is resolved.
-/

section
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
end

-- :TODO:
-- determine what the diamond here is:
example (E : Type) [h₁ : Add E] [Zero E] [One E] [h₂ : Distrib E] [h₃ : Mul E] :
  E :=
sorry
/-
diamond 1:
   Add
   / \
  h₁  h₂
   \ /
    E

diamond 2:
   Mul
   / \
  h₃  h₂
   \ /
    E
-/
--

end diamonds

section simple_example

/-! ## Resolving diamonds (simple example) -/

-- this was how `AddMonoidWithOne` used to be defined 7 months ago in Lean 3:
private class add_monoid_with_one (A : Type) extends AddMonoid A, One A

-- :TODO:
-- show that there exists a type such that `A` is an `add_monoid_with_one` and a `Ring` such that
-- they have different ones
example :
  ∃ (A : Type) (h₁ : add_monoid_with_one A) (h₂ : Ring A), h₁.one ≠ h₂.one :=
⟨ℂ, { one := 0, toAddMonoid := AddLeftCancelMonoid.toAddMonoid },
  Complex.instRingComplex, by norm_num⟩

-- `AddMonoidWithOne` in Lean 4 is stronger
-- however, Lean does not know if the ones are definitionally equal:

example (A : Type) [h₁ : AddMonoidWithOne A] [h₂ : Ring A] :
  h₁.one = h₂.one :=
rfl -- fails

-- :TODO:
-- show that `1 : A` in `AddMonoidWithOne` is `1 : ℕ` coerced into `A`
example (A : Type) [AddMonoidWithOne A] :
  (1 : A) = (1 : ℕ) :=
Nat.cast_one.symm

-- in general:
-- given any classes `classB` and `classC` such that they both extend the same class `sameBC`,
-- then if `classB` and `classC` are instances of `A`, then it does not necessarily mean that
-- the value of `x` from `classB` is the same as the one from `classC`
private class sameBC (A : Type) :=
(x : A)
(add : A → A → A)

private class classB (A : Type) extends sameBC A :=
(p₂ : A → A)
private class classC (A : Type) extends sameBC A :=
(p₃ : A → A → A)

-- :TODO:
example :
  ∃ (A : Type) (hB : classB A) (hC : classC A), hB.x ≠ hC.x :=
⟨ℤ, { x := 0, add := (·+·), p₂ := λ _ => 0},
  { x := 1, add := (·-·), p₃ := λ _ => 0},
  by simp only [ne_eq, zero_ne_one, not_false_eq_true]⟩

 section solution_1
 -- solution 1 - adding the necessary constraints to the statement, for example:
 example (A : Type) (hB : classB A) (hC : classC A) (hBC : hB.x = hC.x) :
   hB.x = hC.x :=
 hBC

 -- in theory, giving the properties of the classes you want as instances to your type
 -- is the safest method for avoiding diamond instance problems

 -- for example, instead of saying `[classA] [classC]` we can write
 -- `(x : A) (add : A → A → A) (p₂ : A → A) (p₃ : A → A → A)`

 -- in practice, however, this is obviously **not** practical, and you most likely will end up
 -- with an error sooner or later
 end solution_1

 section solution_2
 -- solution 2
 private class classE (A : Type) extends classB A, classC A

 -- the above can equivalently be written as:
 private class classE' (A : Type) extends classB A :=
 (p₃ : A → A → A)

 -- now we can show that any type `A` such that `classE A` (which infers both `classB`
 -- and `classC`) will always have the same `x` and `add` properties
 example (A : Type) [h : classE A] :
   h.toclassB.x = (h.toclassC).x :=
 rfl
 example (A : Type) [h : classE A] :
   h.toclassB.add = (h.toclassC).add :=
 rfl

 end solution_2

end simple_example


section resolving_diamonds
/-!
 ## Resolving diamonds (another example)
-/

/-
 We already concluded in the first section that there are non-transparent
  diamonds within our example.

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
@[class, reducible]
structure NormedAddCommGroupOfRing (E : Type*) extends Norm E, Ring E, MetricSpace E :=
dist := fun x y => ‖x - y‖
/-- The distance function is induced by the norm. -/
dist_eq : ∀ x y, dist x y = ‖x - y‖ := by aesop

-- equivalently, we can write the following instead
@[class, reducible] structure NACGoR (E : Type*) extends NormedAddCommGroup E, Ring E

instance NACGoR.inst_Ring {E : Type*} [h : NACGoR E] :
  Ring E :=
h.toRing
instance NACGoR.inst_NormedAddCommGroup {E : Type*} [h : NACGoR E] :
  NormedAddCommGroup E :=
h.toNormedAddCommGroup

/-
 Let's check that we now get the same `AddCommMonoid`:
-/
example {E : Type*} [h : NACGoR E] :
  h.toAddCommMonoid = NormedAddCommGroup.toAddCommGroup.toAddCommMonoid :=
rfl

/-
 We also get the same `AddCommGroup` structure:
-/
example {E : Type*} [NACGoR E] :
  (NormedAddCommGroup.toAddCommGroup : AddCommGroup E) = Ring.toAddCommGroup :=
rfl

/- we have resolved the first diamond! -/

-- this now works!!!
example {E : Type*} [h : NACGoR E] [hE₂ : InnerProductSpace ℂ E] [Algebra ℂ E] [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) :
  LinearMap.adjoint T = 0 := by
{
  let f : E →ₗ[ℂ] E := sorry
  have : LinearMap.adjoint f = T := sorry
  sorry
}

-- but we still have some issues remaining to address:

example {E : Type*} [hE₁ : NACGoR E] [hE₂ : InnerProductSpace ℂ E]
  [hE₃ : Algebra ℂ E] [hE₄ : FiniteDimensional ℂ E]
  (T : E →ₗ[ℂ] E) (x y : E) :
  0 = (LinearMap.adjoint (Algebra.linearMap ℂ E)) x := sorry

/- The error is because of the following non-transparent diamond:
  the module (inferred by the inner product space) is not definitionally equal to that
  inferred by the algebra. -/
example {E : Type*} [NACGoR E]
  [h : InnerProductSpace ℂ E] [Algebra ℂ E] :
  h.toModule = Algebra.toModule :=
rfl -- fails

/-
 `Algebra ℂ A` instance given `A` as a Semiring, `ℂ` Module, and
 has `SMulCommClass ℂ A A` and `IsScalarTower ℂ A A`
 (see [implementation notes](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Algebra/Basic.html#Implementation-notes))
-/
def Algebra.ofModule_inst {R A : Type*} [CommSemiring R] [Semiring A]
  [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] : Algebra R A :=
Algebra.ofModule smul_mul_assoc mul_smul_comm

-- the reason the following is a `local` instance is because you might end up
-- having an infinite recursion of type instances
attribute [local instance] Algebra.ofModule_inst

/-
 Now the module given by the inner product space **is** definitionally equal to that
   inferred by the algebra (which is inferred by the module inferred by the inner producrt space).
-/
example {E : Type*} [NACGoR E] [h : InnerProductSpace ℂ E] [SMulCommClass ℂ E E]
  [IsScalarTower ℂ E E] :
  h.toModule = Algebra.toModule :=
rfl

/- we have now resolved all of our diamonds! -/

-- ay this works now!!! 🎉
example {E : Type*} [hE₁ : NACGoR E] [hE₂ : InnerProductSpace ℂ E]
  [SMulCommClass ℂ E E] [IsScalarTower ℂ E E] [FiniteDimensional ℂ E]
  (T : E →ₗ[ℂ] E) (x y : E) :
  ⟪LinearMap.adjoint T (x * y), T x⟫_ℂ = (LinearMap.adjoint (Algebra.linearMap ℂ E)) x := sorry

end resolving_diamonds
