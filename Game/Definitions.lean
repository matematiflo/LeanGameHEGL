/-!
  # Definitions

  This file contains the core arithmetic definitions used in the game.
  In particular, we define when a natural number is a unit, irreducible, or prime.
-/

namespace Arithmetic

/-- A natural number `n` is a **unit** if there exists a natural number `m` such that
    `m * n = 1` and `n * m = 1`. -/
def unit (n : Nat) : Prop :=
  ∃ m : Nat, m * n = 1 ∧ n * m = 1

/-- A natural number `n` is **irreducible** if, whenever it is written as a product `a * b`,
    at least one of the factors `a` or `b` is a unit. -/
def irred (n : Nat) : Prop :=
  ∀ a b : Nat, n = a * b → unit a ∨ unit b

/-- A natural number `p` is **prime** if it has two properties:
    1. It is positive (`0 < p`).
    2. Whenever `p` divides a product `a * b`, then `p` divides at least one of the factors `a` or `b`. -/
def prime (p : Nat) : Prop :=
  (∀ a b : Nat, p ∣ (a * b) → p ∣ a ∨ p ∣ b) ∧ (0 < p)

end Arithmetic
