import Game.Metadata
import Mathlib.Tactic
import Mathlib.Tactic.Basic -- imports tactics
import Mathlib.Data.Real.Basic -- imports the re

World "MinMaxWorld"
Level 1

Title "The `max` tactic."


open Classical -- allow proofs by contradiction

noncomputable section -- don't fuss about the reals being noncomputable

namespace MyGame -- hide

-- Let a, b, c be real numbers
-- variable {a b c : ℝ}

Introduction "In this chapter we develop a basic interface for the `max a b` and `abs a`
function on the real numbers. Before we start, you will need to know
the basic API for `≤` and `<`, which looks like this:

`example : a ≤ b → b ≤ c → a ≤ c := le_trans`

`example : a ≤ b → b ≤ a → a = b := le_antisymm`

`example : a ≤ b ∨ b ≤ a := le_total a b`

`example : a < b ↔ a ≤ b ∧ a ≠ b := lt_iff_le_and_ne`

`example : a ≤ b → b < c → a < c := lt_of_le_of_lt`

`example : a < b → b ≤ c → a < c := lt_of_lt_of_le`
"

def max (a b : ℝ) := if a ≤ b then b else a
-- TheoremDoc max_eq_right : a ≤ b → max a b = b
-- Statement max_eq_right: a ≤ b → max a b = b := by
-- sorry
-- theorem max_eq_left : b ≤ a → max a b = a
theorem max_eq_right (a b : ℝ) (hab : a ≤ b) : max a b = b :=
  by
    unfold max
    rw [if_pos hab]

theorem max_eq_left (a b : ℝ) (hba : b ≤ a) : max a b = a :=
  by
    by_cases hab : a ≤ b
    -- Case when a ≤ b
    · rw [max_eq_right a b hab]
      exact le_antisymm hba hab
    -- Case when ¬(a ≤ b)
    · unfold max
      rw [if_neg hab]

theorem max_choice (a b : ℝ) : max a b = a ∨ max a b = b :=
  by
    cases le_total a b with
    | inl hab =>
      right
      exact max_eq_right a b hab
    | inr hba =>
      left
      exact max_eq_left a b hba


-- Conclusion "
-- The message shown when the level is completed
-- "
-- TheoremDoc MyGame.obvious as "obvious" in "max"

--  Statement obvious (x: Nat): x = x := by
--   rfl

--  Conclusion "done!"
