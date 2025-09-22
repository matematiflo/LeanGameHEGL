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
  Hint "Construct the three required components of the irreducible definition using the constructor tactic. Use constructor · proof of first statement · proof of second statement · proof of third statement"
  constructor
  · --prime ≠ zero
    Hint "Now, start with proving that p ≠ 0 with the definition of prime."
    Hint (hidden := true) "Use 'apply p_prime.not_zero' to directly use the property from the prime definition."
    apply p_prime.not_zero
  · --prime ¬unit
    Hint "Next, prove that p is not a unit with the defintion of prime."
    apply p_prime.not_unit
  · --a * b = p → unit a ∨ unit b
    Hint "Finally, prove the main irreducibility condition: for any factors a and b such that p = a * b, either a or b is a unit. Start by introducing arbitrary factors a and b and assuming that p = a * b."
    Hint (hidden := true) "Use 'intro a b' to introduce a and b, then 'intro p_is_ab' to assume the equality p = a * b."
    intro a b p_is_ab
    Hint "Apply the 'equality_implies_divide_in_Nat' theorem (from Level 2) to conclude that p divides a * b."
    Hint (hidden := true) "Define an auxiliary statement: 'have p_div_ab : p ∣ (a*b) := ..."
    have p_div_ab : p ∣ (a*b) := by
      Hint "Use Level 2's theorem"
      apply equality_implies_divide_in_Nat p a b
      exact Eq.symm p_is_ab
    Hint "Since p is prime, it must divide at least one of the factors; use that to get p ∣ a ∨ p ∣ b."
    Hint (hidden := true) "Write 'have p_div_a_or_b : p ∣ a ∨ p ∣ b := ..."
    have p_div_a_or_b : p ∣ a ∨ p ∣ b := by
      Hint "Use the property from the prime definition"
      apply p_prime.Euclid
      exact p_div_ab
    Hint "Now, use case analysis on the disjunction p ∣ a ∨ p ∣ b to handle both cases separately. You can do this with rcases {p_div_a_or_b} with p_div_a | p_div_b."
    rcases p_div_a_or_b with p_div_a | p_div_b
    Hint "With case inl => you can go to the case p ∣ a, and with case inr => you can go to the case p ∣ b."
    case inl =>
      Hint "With left or right, you can go to the left or right side of the disjunction unit a ∨ unit b."
      right
      Hint "Now, use Level 4's theorem 'b_unit' to conclude that b is a unit in the case p ∣ a."
      Hint (hidden := true) "You can use 'apply b_unit p a b"
      apply b_unit p a b
      Hint "Now add everything together in one exact statement."
      Hint (hidden := true) "Use exact ⟨{p_prime}, {p_div_a}, Eq.symm {p_is_ab}⟩"
      exact ⟨p_prime, p_div_a, Eq.symm p_is_ab⟩
    case inr =>
      left
      Hint "In the case p ∣ b, use Level 5's theorem 'a_unit' to conclude that a is a unit."
      rewrite [Nat.mul_comm] at p_is_ab
      exact a_unit p a b ⟨p_prime, p_div_b, Eq.symm p_is_ab⟩

Conclusion "
Congratulations! You have shown that every prime number is irreducible.
"

NewTactic apply case left right
NewTheorem a_unit prime_is_irred
