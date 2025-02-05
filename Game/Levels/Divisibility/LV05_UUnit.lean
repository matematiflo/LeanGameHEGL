import Game.Metadata
import Game.Inventory

World "Divisibility"
Level 5

Title "Case 2: Proving u is a Unit"

Introduction "
In this level, we prove that under the following conditions, u is a unit.
That is, if p is prime, p divides v, and p = v * u,
then there exists a number q such that q * u = 1.
"

-- The exercise (or statement) is given below.
Statement u_unit (p u v : Nat) : (prime p) ∧ (p ∣ v) ∧ (p = v * u) → unit u := by
  Hint "Start by introducing the hypothesis into your context."
  Hint (hidden := true) "Use 'intro h' to bring the entire hypothesis into scope."
  intro h
  Hint "Break the hypothesis into its components: p is prime, p divides v, and p = v * u."
  Hint (hidden := true) "Decompose the hypothesis with 'rcases h with ⟨p_prime, p_dvd_v, p_eq_uv⟩'."
  rcases h with ⟨p_prime, p_dvd_v, p_eq_uv⟩
  Hint "From the divisibility p ∣ v, extract a witness q such that v = p * q."
  Hint (hidden := true) "Use 'rcases p_dvd_v with ⟨q, v_eq_pq⟩' to obtain q and the equality v = p * q."
  rcases p_dvd_v with ⟨q, v_eq_pq⟩
  Hint "Simplify the definition of 'unit' (which requires providing an inverse for u)."
  Hint (hidden := true) "Unfold the definition with 'dsimp only [unit]'."
  dsimp only [unit]
  Hint "Provide the witness q to show that u has an inverse."
  Hint (hidden := true) "Use the 'exists' tactic to supply the witness by writing 'exists q'."
  exists q
  Hint "Apply the substitution property (from Level 3) to rewrite p as p * (q * u)."
  Hint (hidden := true) "Define an auxiliary statement with 'have p_eq_pqu : p = p * (q * u) := substitution_in_Nat p q v u ⟨v_eq_pq, p_eq_uv⟩'."
  have p_eq_pqu : p = p * (q * u) := substitution_in_Nat p q v u ⟨v_eq_pq, p_eq_uv⟩
  Hint "Apply the cancellation law (from Level 1) to deduce that 1 = q * u."
  Hint (hidden := true) "Define another auxiliary statement with a 'have' block. Inside the block, use a 'conv' block to rewrite the left-hand side of p_eq_pqu with '← Nat.mul_one p', then apply 'exact cancellation_in_Nat 1 (q * u) p ⟨p_eq_pqu, p_prime.2⟩'. Note that the 'lhs' in the conv block targets the left-hand side of the equality."
  have one_is_qu : 1 = q * u := by
    conv at p_eq_pqu =>
      lhs
      rw [← Nat.mul_one p]
    exact cancellation_in_Nat 1 (q * u) p ⟨p_eq_pqu, p_prime.2⟩
  Hint "Finally, construct the unit instance for u using the equality 1 = q * u."
  Hint (hidden := true) "Use the 'constructor' tactic to build the unit. In the first part, apply the symmetry of one_is_qu, and in the second part, rewrite with 'Nat.mul_comm' before applying the symmetry."
  constructor
  · exact one_is_qu.symm
  · rewrite [Nat.mul_comm]
    exact one_is_qu.symm

Conclusion "
Excellent! You have successfully proven that under the given conditions, u is a unit.
"

NewTheorem v_unit
