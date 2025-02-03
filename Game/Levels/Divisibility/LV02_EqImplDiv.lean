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
Statement (p u v : Nat) : p = u * v → p ∣ (u * v) := by
  Hint "Start by introducing the equality p = u * v into your context."
  intro p_eq_uv
  Hint "Simplify the definition of divisibility. (Recall that p ∣ (u * v) means there exists a k such that p * k = u * v.)"
  dsimp only [Dvd.dvd]
  Hint "Provide the witness (here, 1) that proves the divisibility."
  exists 1
  Hint "Use the fact that multiplying by one does not change a number."
  rewrite [Nat.mul_one p]
  Hint "Finish by using the symmetry of the equality."
  exact Eq.symm p_eq_uv

Conclusion "
Congratulations! You have proven that if p equals u * v, then p divides u * v.
"

NewTactic dsimp rewrite
NewTheorem Nat.mul_one cancellation_in_Nat Eq.symm Dvd.dvd
