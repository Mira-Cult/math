import Shared.Beeping.NPcoNP.Source284ProductIteration
import Shared.ComplexityBridge.ClockBounds

/-! Lower bounds for the token-block sizes produced by the actual fixed-stage
product table. Small inputs require separate constant-workspace handling. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284ProductGrowth

open Shared.Beeping.NPcoNP.Source284ProductIteration

/-- If both input blocks contain at least `n` tokens and `n` is positive,
the newest block grows by at least one factor of `n` at every paid stage. -/
theorem inner_lower (k n a b : Nat) (hn : 1 ≤ n) (ha : n ≤ a) (hb : n ≤ b) :
    b*n^k ≤ innerAfter k a b := by
  induction k generalizing a b with
  | zero => simp [innerAfter]
  | succ k ih =>
    have hb1 : 1 ≤ b := by omega
    have hab : n ≤ a*b := by
      have h := Nat.mul_le_mul_left a hb1
      simp only [Nat.mul_one] at h
      omega
    have hrec := ih b (a*b) hb hab
    have hmul : b*n^(k+1) ≤ (a*b)*n^k := by
      have h := Nat.mul_le_mul_right (b*n^k) ha
      calc
        b*n^(k+1) = n*(b*n^k) := by rw [pow_succ]; ring
        _ ≤ a*(b*n^k) := h
        _ = (a*b)*n^k := by ring
    change b*n^(k+1) ≤ innerAfter k b (a*b)
    exact le_trans hmul hrec

theorem square_seed_lower (k n : Nat) (hn : 1 ≤ n) :
    n^(k+1) ≤ innerAfter k n n := by
  have h := inner_lower k n n n hn (le_refl n) (le_refl n)
  simpa [Nat.pow_succ,Nat.mul_comm] using h

/-- For any fixed polynomial, a fixed number of stages produces at least its
value for every input length `n ≥ 2`. The stage count is selected before the
source program runs. -/
theorem dominates_polynomial (p : Polynomial Nat) :
    ∃ k : Nat, ∀ n : Nat, 2 ≤ n → p.eval n ≤ innerAfter k n n := by
  obtain ⟨e,he⟩ := Shared.ComplexityBridge.ClockBounds.polynomial_fixed_exponent p
  refine ⟨2*e,?_⟩
  intro n hn
  have hbase : n+2 ≤ n*n := by nlinarith
  have hpow := Nat.pow_le_pow_left hbase e
  have hpoweq : (n*n)^e = n^(2*e) := by
    rw [← pow_two,pow_mul]
  rw [hpoweq] at hpow
  have hmore : n^(2*e) ≤ n^(2*e+1) := Nat.pow_le_pow_right (by omega) (by omega)
  exact le_trans (he n) (le_trans hpow (le_trans hmore (square_seed_lower (2*e) n (by omega))))

end Shared.Beeping.NPcoNP.Source284ProductGrowth
