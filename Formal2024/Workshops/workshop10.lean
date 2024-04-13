/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Parity

/-
  # Basic macros & tactics

  See [here](https://leanprover-community.github.io/lean4-metaprogramming-book/md/main/10_cheat-sheet.html) for the Lean 4 metapogramming book's cheat sheet.
-/

macro "rfl_and" : tactic =>
  `(tactic|
      (repeat' apply And.intro
       any_goals rfl))

example :
  2 = 2 ∧ 3 = 3 :=
by rfl_and

macro "even_odd" : tactic =>
  `(tactic|
      (try exact Nat.even_iff.mpr rfl
       try exact Nat.odd_iff.mpr rfl))

example :
  2 = 2 ∧ 1 = 1 ∧ Even 29323542 ∧ 3 = 3 :=
by
  rfl_and
  even_odd

open Lean in
open Lean.Meta in
open Lean.Elab.Tactic in
partial def ifExprAndHyp (h : Expr) : TacticM Bool :=
  withMainContext
  (do
    let a ← inferType h
    let target ← getMainTarget
    let eq ← isDefEq a target
    if eq then
      let goal ← getMainGoal
      MVarId.assign goal h
      return true
    else
      match Expr.and? a with
      | Option.none => return false
      | Option.some (_, _) =>
        let h1 ← mkAppM ``And.left #[h]
        let d ← ifExprAndHyp h1
        if d then
          return true
        else
          let h2 ← mkAppM ``And.right #[h]
          ifExprAndHyp h2)

open Lean in
open Lean.Meta in
open Lean.Elab.Tactic in
def hyp' : TacticM Unit :=
  withMainContext
  (do
    let target ← getMainTarget
    let lctx ← getLCtx
    for ldecl in lctx do
      if ! LocalDecl.isImplementationDetail ldecl then
        let ldeclType := LocalDecl.type ldecl
        let ldeclExpr := LocalDecl.toExpr ldecl
        let h ← getFVarFromUserName (LocalDecl.userName ldecl)

        let d ← ifExprAndHyp h
        let eq ← isDefEq ldeclType target

        if eq then
          let goal ← getMainGoal
          MVarId.assign goal ldeclExpr
          return
        else if d then return
    failure)

elab "hyp'" : tactic =>
  hyp'

macro "hyp" : tactic =>
  `(tactic|
    solve| hyp' | try apply symm; hyp')

example {P Q : Prop} {α : Type _} {r : α → α → Prop} (a b : α) [IsSymm α r] (h : P ∧ r a b ∧ Q) :
  Q :=
by hyp

example {P Q : Prop} {α : Type _} {r : α → α → Prop} (a b : α) [IsSymm α r] (h : P ∧ r a b ∧ Q) :
  P :=
by hyp

example {P Q : Prop} {α : Type _} {r : α → α → Prop} (a b : α) [IsSymm α r] (h : P ∧ r a b ∧ Q) :
  r b a :=
by hyp
