/-
Copyright (c) 2024 TheLeanTeam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Team
-/
import Library

/-!
This file is for showing some examples of how to use the tactic `tada`,
the command `#truth_table`, and the `paperproof` extension.

# Tada! 🎉

`tada` is a tactic that can be used after completing the proof of a theorem to get a
message saying "Goals accomplished 🎉". (People who have used Lean 3 will have missed this!)

Applying the tactic `tada` when the proof is not complete will result in an error message saying
"Goals not accomplished 😢".


# Truth table

`#truth_table` is a command that can be used to generate a truth table for a given proposition.


# Paperproof extension

This is a cool extension that allows you to see your proofs in a paper-like format.
-/

-- `easy_example` is a simple example of a tautological proposition that is easy to prove.
def easy_example (p q : Prop) : Prop := (p → q) ↔ ¬ q → ¬ p

/-!
  # Tada 🎉 examples
-/

-- `tada` example used correctly to prove `easy_example`
lemma easy_example_lemma (p q) : easy_example p q := by
  constructor <;> intro h <;> contrapose! <;> exact h
  tada -- tada message 🎉!

-- `tada` example used incorrectly
example (p q) : easy_example p q := by
  tada -- error message with a sad message 😢

/-!
  # #truth_table examples
-/

-- `#truth_table` example showing `easy_example` is a tautology
#truth_table (p → q) ↔ ¬ q → ¬ p

-- another example of `#truth_table`
#truth_table (P → Q) → (¬ Q → ¬ P) → (P → Q) ∧ (¬ Q → ¬ P)

-- you can also use `#truth_table` to show that a proposition is a contradiction
#truth_table easy_example ∧ ¬ easy_example

-- notice how we used `easy_example` with `#truth_table` above, but we cannot use `easy_example`
-- alone with `#truth_table` to show that it is a tautology because `easy_example` has free variables.
-- In general, you can use the `#truth_table` command with any proposition, but you need to make sure
-- that all the free variables are bound.

-- you shouldn't use `#truth_table` with anything other than propositions however,
-- you cannot use it with `∀` or `∃` quantifiers or with `=` for example
#truth_table 1 + 1 = 2 -- error message
#truth_table ∀ (p : Prop), p -- error message
#truth_table ∃ (p : Prop), p -- error message


/-!
  # Paperproof extension examples
-/

-- click on the "paperproof" button (next to the Lean 4 extension button `∀` above)
-- then you can see the proof in a paper-like format
-- try it out with the following example!
example (p q) : p ∨ ¬ p ↔ easy_example p q := by
  sorry
