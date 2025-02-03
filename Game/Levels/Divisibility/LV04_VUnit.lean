import Game.Metadata
import Game.Inventory
import Game.Levels.Divisibility.LV01_PrimeIrred

World "Divisibility"
Level 4

Title "Proving v is a Unit"

Introduction "
In this level, we prove that under the following conditions v is a unit.
That is, if p is prime, p divides u, and p = u * v, then v must be a unit.
Recall that a number v is a unit if there exists some q with q * v = 1.
"

-- The exercise: prove that if (prime p) ∧ (p ∣ u) ∧ (p = u * v), then v is a unit.
Statement (p u v : Nat) : (prime p) ∧ (p ∣ u) ∧ (p = u * v) → unit v := by
  Hint "Introduce the hypothesis into your context."
  intro h
  Hint "Decompose the hypothesis into its constituent parts."
  rcases h with ⟨p_prime, p_dvd_u, p_eq_uv⟩
  Hint "From the divisibility p ∣ u, extract a witness q such that u = p * q."
  rcases p_dvd_u with ⟨q, u_eq_pq⟩
  Hint "Simplify the definition of unit (which asserts the existence of a multiplicative inverse)."
  dsimp only [unit]
  Hint "Provide the witness q for v being a unit."
  exists q
  Hint "Use the substitution property from Level 3 to obtain an intermediate equality."
  have p_eq_pqv : p = p * (q * v) := substitution_in_Nat p q u v ⟨u_eq_pq, p_eq_uv⟩
  Hint "Apply the cancellation property (from Level 1) to deduce that 1 = q * v."
  have one_is_qv : 1 = q * v := by
    conv at p_eq_pqv =>
      lhs
      rw [← Nat.mul_one p]
    exact cancellation_in_Nat 1 (q * v) p ⟨p_eq_pqv, p_prime.2⟩
  Hint "Finally, conclude by constructing the unit for v."
  constructor
  · exact one_is_qv.symm
  · rewrite [Nat.mul_comm]
    exact one_is_qv.symm

Conclusion "
Excellent! You have successfully proven that under the given conditions v is a unit.
"

-- NewTactic intro rcases dsimp exists have conv constructor rewrite
NewTheorem substitution_in_Nat
