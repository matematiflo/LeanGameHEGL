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
Statement (p u v : Nat) : (prime p) ∧ (p ∣ v) ∧ (p = v * u) → unit u := by
  Hint "Start by introducing the hypothesis into your context."
  intro h
  Hint "Break the hypothesis into its components: the fact that p is prime, p divides v, and p = v * u."
  rcases h with ⟨p_prime, p_dvd_v, p_eq_uv⟩
  Hint "From the divisibility p ∣ v, extract a witness q such that v = p * q."
  rcases p_dvd_v with ⟨q, v_eq_pq⟩
  Hint "Simplify the definition of 'unit' (which requires showing the existence of an inverse)."
  dsimp only [unit]
  Hint "Provide the witness q to show that u has an inverse."
  exists q
  Hint "Apply the substitution property (from Level 3) to rewrite p as p * (q * u)."
  have p_eq_pqu : p = p * (q * u) := substitution_in_Nat p q v u ⟨v_eq_pq, p_eq_uv⟩
  Hint "Apply the cancellation law (from Level 1) to deduce that 1 = q * u."
  have one_is_qu : 1 = q * u := by
    conv at p_eq_pqu =>
      lhs
      rw [← Nat.mul_one p]
    exact cancellation_in_Nat 1 (q * u) p ⟨p_eq_pqu, p_prime.2⟩
  Hint "Finally, construct the unit instance for u using the equality 1 = q * u."
  constructor
  · exact one_is_qu.symm
  · rewrite [Nat.mul_comm]
    exact one_is_qu.symm

Conclusion "
Excellent! You have successfully proven that under the given conditions, u is a unit.
"

NewTheorem v_unit
