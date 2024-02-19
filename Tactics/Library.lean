/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Aesop
import Mathlib.Tactic
-- import AutograderLib
-- import TruthTable
-- import Paperproof


open Lean Elab Tactic

declare_aesop_rule_sets [extra]

macro "aesop" : tactic => `(tactic | fail "aesop tactic disabled")

-- macro "exact?" : tactic => `(tactic | fail "exact? tactic disabled")
-- macro "apply?" : tactic => `(tactic | fail "apply? tactic disabled")

open Lean.Parser.Tactic in
macro "simp" (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*) "]")?
  (location)? : tactic => `(tactic | fail "simp tactic disabled")

@[inline]
elab "tada" : tactic => do
  let gs ← getUnsolvedGoals
  if gs.isEmpty then
    logInfoAt (by assumption) f!"Goals accomplished 🎉"
  else
    logErrorAt (by assumption) f!"Goals remaining 😢"
    -- throwAbortTactic
