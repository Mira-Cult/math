import Shared.Codes.VerifierPrograms

/-! Arithmetic normalization for fixed-exponent candidate clocks. -/
namespace Shared.ComplexityBridge.ClockBounds

/-- A coefficient and a monomial are absorbed uniformly into a fixed exponent. -/
theorem monomial_bound (a d n : Nat) : a * n ^ d ≤ (n + 2) ^ (a + d) := by
  have ha : a ≤ (n + 2) ^ a := by
    exact le_trans (show a ≤ 2 ^ a from Nat.lt_two_pow_self.le)
      (Nat.pow_le_pow_left (show 2 ≤ n + 2 by omega) a)
  have hn : n ^ d ≤ (n + 2) ^ d := Nat.pow_le_pow_left (by omega) d
  calc
    a * n ^ d ≤ (n + 2) ^ a * (n + 2) ^ d := Nat.mul_le_mul ha hn
    _ = (n + 2) ^ (a + d) := by rw [pow_add]

/-- Two fixed-exponent bounds can be absorbed into one larger exponent. -/
theorem add_powers_bound (n a b : Nat) :
    (n + 2) ^ a + (n + 2) ^ b ≤ (n + 2) ^ (max a b + 1) := by
  have hp : 0 < n + 2 := by omega
  have ha := Nat.pow_le_pow_right hp (Nat.le_max_left a b)
  have hb := Nat.pow_le_pow_right hp (Nat.le_max_right a b)
  calc
    (n + 2) ^ a + (n + 2) ^ b ≤ (n + 2) ^ (max a b) + (n + 2) ^ (max a b) := Nat.add_le_add ha hb
    _ = 2 * (n + 2) ^ (max a b) := by omega
    _ ≤ (n + 2) * (n + 2) ^ (max a b) := Nat.mul_le_mul_right _ (by omega)
    _ = (n + 2) ^ (max a b + 1) := by rw [pow_succ]; exact Nat.mul_comm _ _

/-- One exponent, depending only on the polynomial, dominates all inputs. -/
theorem polynomial_fixed_exponent (p : Polynomial Nat) :
    ∃ k : Nat, ∀ n : Nat, p.eval n ≤ (n + 2) ^ k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨max a b + 1, fun n => ?_⟩
    rw [Polynomial.eval_add]
    exact le_trans (Nat.add_le_add (ha n) (hb n)) (add_powers_bound n a b)
  | monomial d a =>
    refine ⟨a + d, fun n => ?_⟩
    rw [Polynomial.eval_monomial]
    exact monomial_bound a d n


/-- Normalize separate witness and encoded-pair polynomials to one exponent. -/
theorem polynomial_pair_common_exponent (witness checker : Polynomial Nat) :
    ∃ k : Nat, ∀ x w : List Bool,
      witness.eval x.length ≤ (x.length + 2) ^ k ∧
      checker.eval (BitstringEncoding.bitEncode (x, w)).length ≤
        ((BitstringEncoding.bitEncode (x, w)).length + 2) ^ k := by
  obtain ⟨a, ha⟩ := polynomial_fixed_exponent witness
  obtain ⟨b, hb⟩ := polynomial_fixed_exponent checker
  refine ⟨max a b, fun x w => ?_⟩
  constructor
  · exact le_trans (ha x.length) (Nat.pow_le_pow_right (by omega) (Nat.le_max_left a b))
  · exact le_trans (hb (BitstringEncoding.bitEncode (x, w)).length)
      (Nat.pow_le_pow_right (by omega) (Nat.le_max_right a b))

/-- Enlarging the witness search is sound only when the original cutoff is
retained. This is a semantic statement, not a compiled wrapper or cost bound. -/
theorem normalized_witness_cutoff (p : Polynomial Nat) :
    ∃ k : Nat, ∀ (x : List Bool) (checker : List Bool → Bool),
      (∃ w, w.length ≤ (x.length + 2) ^ k ∧
        Shared.Codes.VerifierPrograms.cutoffAccept (p.eval x.length) checker w = true) ↔
      ∃ w, w.length ≤ p.eval x.length ∧ checker w = true := by
  obtain ⟨k, hk⟩ := polynomial_fixed_exponent p
  refine ⟨k, fun x checker => ?_⟩
  exact Shared.Codes.VerifierPrograms.cutoff_search_iff _ _ (hk x.length) checker

end Shared.ComplexityBridge.ClockBounds
