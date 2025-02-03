import Game.Metadata
import Game.Inventory

World "Divisibility"
Level 3

Title "Substitution in ℕ"

Introduction "
In this level, we prove a useful substitution property for natural numbers.
If u = p * q and p = u * v, then we can rewrite p as p * (q * v).
"

-- The exercise: prove that from (u = p * q) and (p = u * v) it follows that
-- p = p * (q * v).
Statement (p q u v : Nat) : (u = p * q) ∧ (p = u * v) → p = p * (q * v) := by
  Hint "Introduce the hypothesis into the context."
  intro h
  Hint "Break apart the conjunction in the hypothesis into its components."
  rcases h with ⟨u_eq_pq, p_eq_uv⟩
  Hint "Replace u in the second equality using the fact u = p * q."
  rewrite [u_eq_pq] at p_eq_uv
  Hint "Apply associativity of multiplication to rearrange the product."
  rewrite [Nat.mul_assoc] at p_eq_uv
  Hint "Conclude the proof by using the resulting equality."
  exact p_eq_uv

Conclusion "
Great work! You have established the substitution property in ℕ.
"

-- NewTactic intro rcases rewrite exact
NewTheorem substitution_in_Nat equality_implies_divide_in_Nat Nat.mul_assoc
