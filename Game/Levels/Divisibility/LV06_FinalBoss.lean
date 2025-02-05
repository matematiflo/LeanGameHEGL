import Game.Metadata
import Game.Inventory

World "Divisibility"
Level 6

Title "Prime Implies Irreducible"

Introduction "
In this final level, we prove that every prime number is irreducible.
That is, if a number p is prime, then for any factorization p = u * v, at least one of u or v must be a unit.
This is a key property in number theory.
"

-- The exercise (or statement) is given below.
/-- Final Boss -/
Statement prime_is_irred (p : Nat) : prime p → irred p := by
  Hint "Begin by assuming that p is prime."
  Hint (hidden := true) "Start with 'intro p_prime' to assume that p is prime and add it to your context."
  intro p_prime
  Hint "Unfold the definition of irreducible for p."
  Hint (hidden := true) "Use 'dsimp only [irred]' to reveal the structure of irreducibility."
  dsimp only [irred]
  Hint "Now introduce arbitrary factors u and v and assume that p = u * v."
  Hint (hidden := true) "Use 'intro u v' to introduce u and v, then 'intro p_is_uv' to assume the equality p = u * v."
  intro u v
  intro p_is_uv
  Hint "Apply the 'equality_implies_divide_in_Nat' theorem (from Level 2) to conclude that p divides u * v."
  Hint (hidden := true) "Define an auxiliary statement: 'have p_div_uv : p ∣ u * v := equality_implies_divide_in_Nat p u v p_is_uv'."
  have p_div_uv : p ∣ u * v := equality_implies_divide_in_Nat p u v p_is_uv
  Hint "Since p is prime, it must divide at least one of the factors; use that to get p ∣ u ∨ p ∣ v."
  Hint (hidden := true) "Write 'have p_div_u_or_v : p ∣ u ∨ p ∣ v := p_prime.1 u v p_div_uv' to derive the disjunction."
  have p_div_u_or_v : p ∣ u ∨ p ∣ v := p_prime.1 u v p_div_uv
  Hint "Perform a case analysis on whether p divides u or p divides v."
  Hint (hidden := true) "Use 'rcases p_div_u_or_v with p_div_u | p_div_v' to split the disjunction into two cases. The labels 'inl' and 'inr' indicate the left and right cases, respectively: 'inl' corresponds to p ∣ u and 'inr' corresponds to p ∣ v."
  rcases p_div_u_or_v with p_div_u | p_div_v
  case inl =>
    Hint "If p divides u, then Level 4’s result 'v_unit' tells us that v is a unit."
    Hint (hidden := true) "In the 'inl' case (the left side of the disjunction), choose the right disjunct with 'right' and apply 'v_unit' with the appropriate arguments."
    right
    apply v_unit
    exact ⟨p_prime, p_div_u, p_is_uv⟩
  case inr =>
    Hint "If p divides v, then by rewriting p = u * v (using commutativity) and applying Level 5’s result 'u_unit', we conclude that u is a unit."
    Hint (hidden := true) "In the 'inr' case (the right side of the disjunction), choose the left disjunct with 'left'. Then, rewrite the equality using 'rewrite [Nat.mul_comm] at p_is_uv' and apply 'u_unit' with the proper arguments."
    left
    rewrite [Nat.mul_comm] at p_is_uv
    exact u_unit p u v ⟨p_prime, p_div_v, p_is_uv⟩


Conclusion "
Congratulations! You have shown that every prime number is irreducible.
"

NewTactic apply case left right
NewTheorem u_unit prime_is_irred
