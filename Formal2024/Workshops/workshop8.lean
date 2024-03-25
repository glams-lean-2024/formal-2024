/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-
  # Practical stuff

  This week we will look at some practical aspects of Lean. These are:
  · Organising and importing files
  · Attributes and the simplifier
  · Defining your own notation

  After this, you will have time to work on your projects. Alternatively, if you are not planning
  to do a project (or even if you are), we encourage you to work through the [MIL] section on
  topology. This will introduce the idea of filter and their convergence, which is used in the
  *mathlib*'s treatment of topololgy. There is a challenge exercise at the end of this file to
  check your understanding of filters.
-/

/-
  ## Organising and importing files

  The main organisational tools in Lean are the *section* and the *namespace*.
  The best references for this are:
  [TPL](https://lean-lang.org/theorem_proving_in_lean4/interacting_with_lean.html)
  [Manual](https://lean-lang.org/lean4/doc/organization.html)
-/

-- Sections can have an optional name, which you need to use when you close them.
section foo

-- Variable declarations are scoped to the current section or namespace.
universe u
variable {α : Type u} (x : α)

def bar : x = x := rfl
#check bar

variable (α)

def baz : x = x := rfl
#check baz

#check Type u

end foo

/-
  Once the section is closed, the variables are no longer available, but the definitions are.
  Uncomment these lines to see the errors.
-/
-- #check α
-- #check Type u
#check bar
#check baz

/-
  Namespaces are similar to sections, but they will add a prefix to any definitions inside.
  Recall that everytime we define an inductive type, structure or class, Lean automatically
  creates a namespace with the same name, where useful definitions and theorems are stored, e.g.
  the constructors and recursors.
-/

namespace foo

def bar (n : ℕ) : n + n = 2 * n := (Nat.two_mul n).symm
def qux : 1 + 1 = 2 := rfl

end foo

-- We now have both `bar` and `foo.bar`.
#check bar
#check foo.bar
#check foo.qux

/-
  If we want to use the definitions inside a namespace without prefixing them, we can *open* the
  namespace. It will stay open inside the current section/namespace. This can lead to name clashes,
  in which case Lean will attempt to disambiguate depending on the type of the expression.
-/

section

-- We can only make some of the definitions in the namespace available as follows:
open foo (qux)

#check qux
#check bar

open foo

-- The next two uses of `bar` refer to two different `bar`s!
#check bar
example : 0 = 0 := bar _

end

/-
  One can also export definitions from a namespace to the current namespace. This will not only
  make them available without prefixing inside the namespace, but also anytime the namespace is
  opened.
-/
namespace foo
export Nat (zero succ)
#check zero
#check succ
end foo

section
-- #check zero
-- #check zero
open foo
#check zero
#check succ
end

/-
  To use declarations in another file, you need to import the file using `import`. This must be
  done at the beginning of the file. What files can be imported depends on the configuration of
  your project, which is specified in `lakefile.lean`.

  File imports are transitive, so if a file `A.lean` imports `B.lean`, then importing `A.lean` will
  also make the declarations in `B.lean` available.

  When importing files from *mathlib* it is a good idea to import only what you need and revise
  if any of your imports become redundant when adding new ones.
-/


/-
  ## Attributes and the simplifier

  Attributes are modifiers that can be attached to declarations. We have already seen some of them,
  like the `@[class]` attribute. Here we will mention the most common one, and how to use them.
-/

/-
  To attach an attribute to a definition, we precede the definition by `@[attr]`, where `attr` is
  the name of the attribute.

  One can also attach an attribute after the definition has been made, using the `attribute`
  keyword. This notation allows us to mark declarations with attributes locally within the current
  section/namespace, by prepending the keyword `local` before the attribute name.
-/

section classes

-- `@[class]` declares that a definition of a structure is a class.
-- It is equivalent to using the `class` keyword.
@[class] structure isPrime (n : ℕ) : Prop where
  is_prime : ∀ m, m ∣ n → m = 1 ∨ m = n

class isPrime' (n : ℕ) : Prop where
  is_prime : ∀ m, m ∣ n → m = 1 ∨ m = n

-- `@[instance]` declares that a definition is an instance of a class.
-- It is equivalent to using the `instance` keyword.
@[instance] def twoPrime : isPrime 2 := sorry

instance threePrime : isPrime 3 := sorry

def fivePrime : isPrime 5 := sorry

attribute [instance] fivePrime

#instances isPrime

end classes

section coe

/-
  The `@[coe]` attribute can be attached to functions to have them print more nicely when coercing.
-/

structure PrimeNat where
  value : ℕ
  is_prime : Nat.Prime value

/-
  The `Coe` typeclass is used to define coercions. An instance of `Coe α β` allows us to treat
  terms of type `α` as terms of type `β`.
-/
instance : Coe PrimeNat ℕ where
  coe p := p.value

def two : PrimeNat := ⟨2, Nat.prime_two⟩

#check (two : ℕ)
-- However, the coercion is not printed in a nice way. This can be fixed with the `@[coe]`
-- attribute.

attribute [coe] PrimeNat.value
#check (two : ℕ)
-- This gives us the `↑` notation for coercions.

end coe

/-
  The remaining attributes we will talk about are linked to tactics. They are attached to lemmas
  that we want the respective tactics to be aware of.

  · The `@[ext]` attribute is used to declare that a lemma is an extensionality lemma. It will then
    be applied by the `ext` tactic when the types match.
  · The `@[symm]` attribute is used to declare that a lemma is a symmetry lemma. It will then be
    applied by the `symm` tactic.

  The most important one of these is the `@[simp]` attribute. It makes the marked lemma available
  to the *simplifier*, which can be invoked with the `simp` tactic. In this course, `simp` is
  disabled by the `Library` file, so we haven't imported it in this file.
-/

/-
  The *simplifier* is aware of hundreds (if not thousands) of `@[simp]`-marked lemmas that it can
  use to rewrite an expression into something (hopefully) simpler. Its power stems from the fact
  that you can add your own lemmas to the simplifier, so it becomes aware of your own definitions.

  As with `rw` you can provide lemmas to the `simp` tactic manually when you use it, by using `[]`.
  However, if you find that you are using the same lemmas over and over, there is a good chance
  they deserve to me marked with the `@[simp]` attribute.

  You can use the `simp?` tactic to see what lemmas `simp` is using. You can also use the `#simp`
  command to see how `simp` would simplify a given expression.
-/

section simp

variable {G : Type} [Group G] (x : G)

example : x * 1 * x⁻¹ = x⁻¹ * 1 * 1 * x := by simp?
-- The lemmas on the output list are all marked with `@[simp]`.

#simp x * (1 * x) * x⁻¹

/-
  We can't just make any lemma a `simp` lemma. Its conclusion needs to be an equality or iff.
  Moreover, for a lemma to be useful to `simp`, the RHS of this equality should be 'simpler' than
  the LHS. Of course, this is just a heuristic, but it is usually good enough.
-/

-- For example, this lemma is a good candidate for a `simp` lemma.
example (n : ℕ) : n + 0 = n := by simp?

-- But this one is not.
lemma not_simp (n : ℕ) : n = n + 0 := by simp?

-- If both of these were `simp` lemmas, `simp` could get stuck in an infinite loop.
-- Let's test this by making the bad lemma a `simp` lemma locally.
attribute [local simp] not_simp

-- The following example will give a maximum recursion reached error because of this.
-- example (n : ℕ) : n = 0 + n := by simp

end simp


/-
  ## Defining your own notation

  To use symbols such as `+`, `*`, `Σ`, `Π` in Lean, they need to be declared as custom notation.
  This can be done using the `notation` command and its various incarnations.
-/

-- This is how one can define binary, prefix and postfix operators.
infixl:65   " + " => HAdd.hAdd  -- left-associative
infix:50    " = " => Eq         -- non-associative
infixr:80   " ^ " => HPow.hPow  -- right-associative
prefix:100  "-"   => Neg.neg
postfix:max "⁻¹"  => Inv.inv

-- Note that we can only assign notation to functions that are already defined.

-- The previous lines are equivalent to these, which use the full `notation` command.
notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs
notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs
notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
notation:100 "-" arg:100 => Neg.neg arg
notation:1024 arg:1024 "⁻¹" => Inv.inv arg

-- Lean allows us to define more complicated notation, such as `Σ x in S, f x`. This is done more
-- generally using macros, which we won't cover here. If you want to learn more about them, check
-- [Manual](https://lean-lang.org/lean4/doc/macro_overview.html) and compare it to the file
-- imported on line 7, where the `Σ` notation is defined.


/-
  ## Challenge

  If you don't have a project to work on, or if you are intersted in seeing how topology is dealt
  with in *mathlib*, this is for you! It is an open ended, self-guided exercise that will get you
  used to filter and how they are used in Lean.

  1. Work through
     [MIL Topology](https://leanprover-community.github.io/mathematics_in_lean/C09_Topology.html)
     for as a long as you are interested.

  2. Check out how the sum of series is defined in *mathlib* in the file imported on line 8, or
     alternatively in the
     [docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/Basic.html).
     Note that this is not the usual way we define the sum of a convergent series. This definition
     is stronger because it doesn't depend on the order of the terms.

  3. Check out the following lemma and either understand its proof or try to prove it yourself.
     This shows that *mathlib*'s definition of the sum of a series implies the usual one.
-/

#check HasSum.tendsto_sum_nat
