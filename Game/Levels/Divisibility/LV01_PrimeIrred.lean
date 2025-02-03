import Game.Metadata
import Game.Inventory

World "Divisibility"
Level 1

Title "Cancellation in ℕ"

Introduction "
In this level, we prove the cancellation law for natural numbers.
That is, if multiplying two numbers by a positive number gives the same result,
then the original numbers must be equal.
"

-- The exercise (or statement) is given below.
Statement (a b c : Nat) : (c * a = c * b) ∧ (0 < c) → a = b := by
  Hint "Use 'intro' to move the antecedent of the implication into your context."
  intro h
  Hint "Start by breaking apart the hypothesis h into its two components."
  rcases h with ⟨ca_eq_cb, zero_smaller_c⟩
  Hint "Now apply the function `Nat.mul_left_cancel`."
  exact Nat.mul_left_cancel zero_smaller_c ca_eq_cb

Conclusion "
Well done! You have successfully proven that cancellation holds in ℕ.
"

NewTactic intro rcases exact
NewTheorem Nat.mul_left_cancel
NewDefinition unit irred prime
