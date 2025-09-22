import Game.Metadata
import Game.Inventory

World "Divisibility"
Level 1

Title "Cancellation in ℕ"

Introduction "
In this level, we prove the cancellation law for natural numbers.
That is, if multiplying two numbers by a non zero natural number gives the same result,
then the original numbers must be equal.
"
-- The exercise (or statement) is given below.
Statement cancellation_in_Nat (a b c : Nat) : (c * a = c * b) ∧ (c ≠ 0) → a = b := by
  Hint "Use 'intro h', this creates a new element h to your local context."
  intro h
  Hint "Start by breaking apart the proof h into its two components. Use rcases {h} with ⟨ ca_eq_cb, c_ne_0 ⟩"
  rcases h with ⟨ca_eq_cb, c_ne_zero⟩
  Hint "We want to use Nat.mul_left_cancel, but for that, we need that c is positive. You can add a new proposition with have. The syntax is `have name : statement := proof`."
  Hint (hidden := true) "Use have c_pos : 0 < c := Nat.pos_of_ne_zero {c_ne_zero}"
  have c_pos : 0 < c := Nat.pos_of_ne_zero c_ne_zero
  Hint "Now you can use Nat.mul_left_cancel to finish the proof. You can do this with the exact tactic."
  Hint (hidden := true) "Use exact Nat.mul_left_cancel {c_pos} {ca_eq_cb}"
  exact Nat.mul_left_cancel c_pos ca_eq_cb

Conclusion "
Well done! You have successfully proven that cancellation holds in ℕ.
"

NewTactic intro rcases exact «have»
NewTheorem Nat.mul_left_cancel Nat.pos_of_ne_zero
NewDefinition unit irred prime
