import Game.Metadata
import Game.Inventory

World "Divisibility"
Level 2

Title "Equality Implies Divisibility"

Introduction "
In this level, we prove that if a natural number p equals the product of two numbers u and v,
then p divides the product u * v.
"

-- The exercise (or statement) is given below.
Statement equality_implies_divide_in_Nat (p u v : Nat) : p = u * v → p ∣ (u * v) := by
  Hint "Start by introducing a proof of the equality p = u * v into your context."
  Hint (hidden := true) "Introduce the hypothesis with 'intro p_eq_uv'."
  intro p_eq_uv
  Hint "Simplify the definition of divisibility. (Recall that p ∣ (u * v) means there exists a natural number k such that p * k = u * v.)"
  Hint (hidden := true) "Use 'dsimp only [Dvd.dvd]' to unfold the definition and expose the existential quantifier."
  dsimp only [Dvd.dvd]
  Hint "Provide a witness for the existential quantifier. Here, the number 1 will work."
  Hint (hidden := true) "The 'exists' tactic allows you to supply a specific value for the existential statement. In this case, write 'exists 1'."
  exists 1
  Hint "Use the fact that multiplying by one does not change a number to simplify the equation."
  Hint (hidden := true) "Rewrite using 'rewrite [Nat.mul_one {p}]' to convert p * 1 to p."
  rewrite [Nat.mul_one p]
  Hint "Finish by applying the symmetry of the equality to conclude the proof."
  Hint (hidden := true) "With 'exact Eq.symm {p_eq_uv}' you can complete the proof."
  exact Eq.symm p_eq_uv



Conclusion "
Congratulations! You have proven that if p equals u * v, then p divides u * v.
"

NewTactic dsimp rewrite «exists»
NewTheorem Nat.mul_one cancellation_in_Nat Eq.symm Dvd.dvd
