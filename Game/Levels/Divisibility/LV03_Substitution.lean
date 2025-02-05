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
Statement substitution_in_Nat (p q u v : Nat) : (u = p * q) ∧ (p = u * v) → p = p * (q * v) := by
  Hint "Introduce the hypothesis into the context."
  Hint (hidden := true) "Use 'intro h' to bring the conjunction (u = p * q) ∧ (p = u * v) into scope."
  intro h
  Hint "Break apart the conjunction in the hypothesis into its components."
  Hint (hidden := true) "Apply 'rcases h with ⟨u_eq_pq, p_eq_uv⟩' to extract both equalities, so you have u_eq_pq : u = p * q and p_eq_uv : p = u * v."
  rcases h with ⟨u_eq_pq, p_eq_uv⟩
  Hint "Replace u in the second equality with p * q using the equality u = p * q."
  Hint (hidden := true) "Execute 'rewrite [u_eq_pq] at p_eq_uv' to substitute u with p * q in p_eq_uv."
  rewrite [u_eq_pq] at p_eq_uv
  Hint "Apply the associativity of multiplication to rearrange the product into the desired form."
  Hint (hidden := true) "Use 'rewrite [Nat.mul_assoc] at p_eq_uv' so that p_eq_uv becomes p = p * (q * v)."
  rewrite [Nat.mul_assoc] at p_eq_uv
  Hint "Conclude the proof by using the equality obtained."
  Hint (hidden := true) "Finish with 'exact p_eq_uv' to complete the proof."
  exact p_eq_uv


Conclusion "
Great work! You have established the substitution property in ℕ.
"

-- NewTactic intro rcases rewrite exact
NewTheorem substitution_in_Nat equality_implies_divide_in_Nat Nat.mul_assoc
