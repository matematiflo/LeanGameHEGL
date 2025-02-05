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
Statement cancellation_in_Nat (a b c : Nat) : (c * a = c * b) ∧ (0 < c) → a = b := by
  Hint "Use 'intro p', this creates a new element p to your local context."
  intro p
  Hint "Start by breaking apart the proof p into its two components. Use rcases"
  Hint (hidden := true) "You use rcases by breaking your hypothesis into two components that you can name to reference them in subsequent steps. Here you could write 'rcases p with ⟨ca_eq_cb, zero_smaller_c⟩' "
  rcases p with ⟨ca_eq_cb, zero_smaller_c⟩
  Hint "Now apply the cancellation property: if 0 < c and c * a = c * b, then a = b. Use Nat.mul_left_cancel"
  Hint (hidden := true) "With the 'exact' tactic, you can finish the proof by directly applying Nat.mul_left_cancel. 'exact Nat.mul_left_cancel zero_smaller_c ca_eq_cb"
  exact Nat.mul_left_cancel zero_smaller_c ca_eq_cb

Conclusion "
Well done! You have successfully proven that cancellation holds in ℕ.
"

NewTactic intro rcases exact
NewTheorem Nat.mul_left_cancel
NewDefinition unit irred prime
