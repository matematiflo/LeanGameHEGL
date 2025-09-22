import Game.Metadata
import Game.Inventory

World "Divisibility"
Level 5

Title "Case 2: Proving a is a Unit"

Introduction "
In this level, we prove that under the following conditions, a is a unit.
That is, if p is prime, p divides b, and p = b * a,
then there exists numbers m and k such that m * a = a * k = 1.
"

-- The exercise (or statement) is given below.
Statement a_unit (p a b : Nat) : (prime p) ∧ (p ∣ b) ∧ (p = b * a) → unit a := by
  Hint "Start by introducing the hypothesis into your context."
  Hint (hidden := true) "Use 'intro h' to bring the entire hypothesis into scope."
  intro h
  Hint "Break the hypothesis into its components: p is prime, p divides b, and p = b * a."
  Hint (hidden := true) "Decompose the hypothesis with 'rcases {h} with ⟨p_prime, p_dvd_b, p_eq_ba⟩'."
  rcases h with ⟨p_prime, p_dvd_b, p_eq_ba⟩
  Hint "From the divisibility p ∣ b, extract a witness c such that b = p * c."
  Hint (hidden := true) "Use 'rcases p_dvd_b with ⟨c, b_eq_pc⟩' to obtain c and the equality b = p * c."
  rcases p_dvd_b with ⟨c, b_eq_pc⟩
  Hint "Simplify the definition of 'unit' (which requires providing an inverse for u)."
  Hint (hidden := true) "Unfold the definition with 'dsimp only [unit]'."
  dsimp only [unit]
  Hint "Construct the two required components of the unit definition using the constructor tactic. Use constructor · proof of first statement · proof of second statement"
  constructor
  · --∃ m : Nat, m * n = 1
    Hint "Provide the witness {c} for a being a unit."
    exists c
    Hint "Apply the substitution property (from Level 3) to rewrite p as p * ({c} * a)."
    have p_eq_pca : p = p * (c * a) := substitution_in_Nat p c b a ⟨b_eq_pc, p_eq_ba⟩
    Hint "Apply the cancellation law (from Level 1) to deduce that {c} * a = 1."
    have ca_is_one : c * a = 1 := by
      conv at p_eq_pca =>
        lhs
        rw [← Nat.mul_one p]
      exact cancellation_in_Nat (c * a) 1 p ⟨Eq.symm p_eq_pca, p_prime.not_zero⟩
    exact ca_is_one
  · --∃ k : Nat, n * k = 1
    Hint "Again, provide the witness {c} for a being a unit."
    exists c
    Hint "Use the substitution property (from Level 3) to rewrite p as p * ({c} * a)."
    have p_eq_pca : p = p * (c * a) := substitution_in_Nat p c b a ⟨b_eq_pc, p_eq_ba⟩
    Hint "Now, we need to prove 1 = {c} * a. We can use the same approach as before, but we will need to apply symmetry at the end."
    have one_is_ca : 1 = c * a := by
      Hint "Start by applying symmetry to reverse the equality."
      Hint (hidden := true) "Use 'apply Eq.symm' to swap both sides of the equality."
      apply Eq.symm
      conv at p_eq_pca =>
        lhs
        rw [← Nat.mul_one p]
      Hint "Apply the cancellation law (from Level 1) to deduce that 1 = {c} * a."
      Hint (hidden := true) "Use 'exact cancellation_in_Nat ({c} * a) 1 p ⟨Eq.symm {p_eq_pca}, {p_prime}.not_zero⟩' to finish this part of the proof."
      exact cancellation_in_Nat (c * a) 1 p ⟨Eq.symm p_eq_pca, p_prime.not_zero⟩

    rw [Nat.mul_comm]
    apply one_is_ca.symm


Conclusion "
Excellent! You have successfully proven that under the given conditions, a is a unit.
"

NewTheorem b_unit
