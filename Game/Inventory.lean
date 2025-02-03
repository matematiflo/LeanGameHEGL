import Game.Metadata

/-- This theorem allows you to cancel a positive multiplier from both sides of an equality in ℕ. -/
TheoremDoc Nat.mul_left_cancel as "Nat.mul_left_cancel" in "Nat"

/-- This theorem allows you to cancel a positive multiplier from both sides of an equality in ℕ. -/
TheoremDoc Nat.mul_one as "Nat.mul_one" in "Nat"

/-- Test Test T3st -/
TheoremDoc substitution_in_Nat as "substitution_in_Nat" in "Level 3"

/-- A number n is a unit if there exists an m such that m * n = 1 and n * m = 1. -/
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

/-- Test Cancel stuff -/
def cancellation_in_Nat (a b c : Nat) : (c * a = c * b) ∧ (0 < c) → a = b := by
  intro h
  rcases h with ⟨ca_eq_cb , zero_smaller_c⟩
  exact Nat.mul_left_cancel zero_smaller_c ca_eq_cb


/-- Test Cancel stuff -/
def substitution_in_Nat (p q u v : Nat) : (u = p * q) ∧ (p = u * v) → p = p * (q * v) := by
  intro h
  rcases h with ⟨u_eq_pq , p_eq_uv⟩
  rewrite [u_eq_pq] at p_eq_uv
  rewrite [Nat.mul_assoc] at p_eq_uv
  exact p_eq_uv
