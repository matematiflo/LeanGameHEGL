import Game.Metadata
-- Level 1
/-- This theorem allows you to cancel a positive multiplier from both sides of an equality in ℕ. -/
TheoremDoc Nat.mul_left_cancel as "Nat.mul_left_cancel" in "Lean"

-- Level 2
/-- This theorem allows you to cancel a positive multiplier from both sides of an equality in ℕ. -/
TheoremDoc Nat.mul_one as "Nat.mul_one" in "Lean"

TheoremDoc Eq.symm as "Eq.symm" in "Lean"
TheoremDoc Dvd.dvd as "Dvd.dvd" in "Lean"

-- Level 3
/--
Multiplication is associative in ℕ.
That is, for all natural numbers a, b, and c,
  (a * b) * c = a * (b * c).
-/
TheoremDoc Nat.mul_assoc as "Nat.mul_assoc" in "Lean"

-- Level 4
/--
Multiplication is commutative in ℕ.
That is, for all natural numbers a and b,
  a * b = b * a.
-/
TheoremDoc Nat.mul_comm as "Nat.mul_comm" in "Lean"



-- Theorems proved in the Levels

/--
This theorem, proved in Level 1, states that if
  c * a = c * b
and
  0 < c,
then we can cancel c to conclude that a = b.
-/
TheoremDoc cancellation_in_Nat as "cancellation_in_Nat" in "Levels"

/--
This theorem, proved in Level 2, shows that if a number p equals the product u * v,
then p divides u * v.
-/
TheoremDoc equality_implies_divide_in_Nat as "equality_implies_divide_in_Nat" in "Levels"

/--
This theorem, proved in Level 3, establishes a substitution property:
if u = p * q and p = u * v, then p = p * (q * v).
-/
TheoremDoc substitution_in_Nat as "substitution_in_Nat" in "Levels"

/--
This theorem, proved in Level 4, shows that under the conditions
  p is prime,
  p divides u, and
  p = u * v,
the number v is a unit.
-/
TheoremDoc v_unit as "v_unit" in "Levels"

/--
This theorem, proved in Level 5, shows that if
  p is prime,
  p divides v, and
  p = v * u,
then u is a unit.
-/
TheoremDoc u_unit as "u_unit" in "Levels"

/-- Theorem proves in Level 6
  -/
TheoremDoc prime_is_irred as "prime_is_irred" in "Levels"


--Definitions

/-- A number n is a **unit** if there exists an m such that m * n = 1 and n * m = 1. -/
def unit (n : Nat) : Prop :=
  ∃ m : Nat, m * n = 1 ∧ n * m = 1

/-- A number n is irreducible if, whenever n = a * b, then either a or b is a unit. -/
def irred (n : Nat) : Prop :=
  ∀ a b : Nat, n = a * b → unit a ∨ unit b

/-- A number p is prime if it divides any product only when it divides at least one factor and if p > 0. -/
def prime (p : Nat) : Prop :=
  (∀ a b : Nat, p ∣ (a * b) → p ∣ a ∨ p ∣ b)
  ∧ 0 < p
-- DefinitionDoc prime as "prime"


/-- Level 1 -/
def cancellation_in_Nat (a b c : Nat) : (c * a = c * b) ∧ (0 < c) → a = b := by
  intro h
  rcases h with ⟨ca_eq_cb , zero_smaller_c⟩
  exact Nat.mul_left_cancel zero_smaller_c ca_eq_cb

/-- Level 2 -/
def equality_implies_divide_in_Nat (p u v : Nat) : p = u * v → p ∣ u * v := by
  intro p_eq_uv
  dsimp only [Dvd.dvd]
  exists 1
  rewrite[Nat.mul_one p]
  exact Eq.symm p_eq_uv

/-- Level 3 -/
def substitution_in_Nat (p q u v : Nat) : (u = p * q) ∧ (p = u * v) → p = p * (q * v) := by
  intro h
  rcases h with ⟨u_eq_pq , p_eq_uv⟩
  rewrite [u_eq_pq] at p_eq_uv
  rewrite [Nat.mul_assoc] at p_eq_uv
  exact p_eq_uv

/-- Level 4 -/
def v_unit (p u v : Nat) : (prime p) ∧ (p ∣ u) ∧ (p = u * v) → unit v := by
  intro h
  rcases h with ⟨p_prime, p_dvd_u , p_eq_uv⟩
  rcases p_dvd_u with ⟨q, u_eq_pq⟩
  dsimp only [unit]
  exists q
  have p_eq_pqv : p = p * (q * v) := substitution_in_Nat p q u v ⟨u_eq_pq , p_eq_uv⟩
  have one_is_qv : 1 = q * v := by
    conv at p_eq_pqv =>
    lhs
    rw [← Nat.mul_one p]
    exact cancellation_in_Nat 1 (q * v) p ⟨p_eq_pqv , p_prime.2⟩
  constructor
  · exact one_is_qv.symm
  · rewrite [Nat.mul_comm]
    exact one_is_qv.symm

/-- Level 5 -/
def u_unit (p u v : Nat) : (prime p) ∧ (p ∣ v) ∧ (p = v * u) → unit u := by
  intro h
  rcases h with ⟨ p_prime, p_dvd_v , p_eq_uv ⟩
  rcases p_dvd_v with ⟨q, v_eq_pq⟩
  dsimp only [unit]
  exists q
  have p_eq_pqu : p = p * (q * u) := substitution_in_Nat p q v u ⟨v_eq_pq , p_eq_uv⟩
  have one_is_qu : 1 = q * u := by
    conv at p_eq_pqu =>
    lhs
    rw [← Nat.mul_one p]
    exact cancellation_in_Nat 1 (q * u) p ⟨p_eq_pqu , p_prime.2⟩
  constructor
  · exact one_is_qu.symm
  · rewrite [Nat.mul_comm]
    exact one_is_qu.symm
