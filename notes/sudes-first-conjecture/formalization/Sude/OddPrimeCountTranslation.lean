import Sude.PoolPartialSummation
import Mathlib.NumberTheory.PrimeCounting

/-! Exact translation between the project's odd-prime prefix and mathlib's
natural prime-counting function. No analytic prime-count estimate is used. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- The odd-prime count is zero at the endpoints below the omitted prime 2. -/
theorem oddPrimePrefix_card_eq_zero_of_lt_two {k : ℕ} (hk : k < 2) :
    (oddPrimePrefix k).card = 0 := by
  have hempty : oddPrimePrefix k = ∅ := by
    ext p
    simp only [oddPrimePrefix, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
    rintro ⟨hp, hprime, _⟩
    have htwo := hprime.two_le
    omega
  simp [hempty]

/-- At and above 2, mathlib's closed-endpoint count is exactly the odd-prime
count plus the omitted prime 2. -/
theorem primeCounting_eq_oddPrimePrefix_add_one {k : ℕ} (hk : 2 ≤ k) :
    Nat.primeCounting k = (oddPrimePrefix k).card + 1 := by
  exact prime_count_succ_eq_oddPrefix_add_one hk

/-- For every natural endpoint, including 0 and 1, truncating subtraction
correctly removes prime 2 from mathlib's count. -/
theorem oddPrimePrefix_card_eq_primeCounting_sub_one (k : ℕ) :
    (oddPrimePrefix k).card = Nat.primeCounting k - 1 := by
  by_cases hk : 2 ≤ k
  · rw [primeCounting_eq_oddPrimePrefix_add_one hk]
    omega
  · have hz := oddPrimePrefix_card_eq_zero_of_lt_two (show k < 2 by omega)
    have hp : Nat.primeCounting k = 0 := Nat.primeCounting_eq_zero_iff.mpr (by omega)
    simp [hz, hp]

/-- The real-valued version makes the correction for 2 explicit; in
particular it never subtracts 1 at the small endpoints. -/
theorem oddPrimePrefix_card_real_eq_primeCounting (k : ℕ) :
    ((oddPrimePrefix k).card : ℝ) = (Nat.primeCounting k : ℝ) - (if 2 ≤ k then 1 else 0) := by
  by_cases hk : 2 ≤ k
  · have h := primeCounting_eq_oddPrimePrefix_add_one hk
    have hr : (Nat.primeCounting k : ℝ) = ((oddPrimePrefix k).card : ℝ) + 1 := by exact_mod_cast h
    simp only [if_pos hk]
    linarith
  · have hz := oddPrimePrefix_card_eq_zero_of_lt_two (show k < 2 by omega)
    have hp : Nat.primeCounting k = 0 := Nat.primeCounting_eq_zero_iff.mpr (by omega)
    simp [hz, hp, hk]

/-- At the actual pool maximum, the complete prime count consists of all
`n²` odd pool entries and prime 2, including the empty pool case `n=0`. -/
theorem primeCounting_poolMaximum (n : ℕ) :
    Nat.primeCounting (poolMaximum n) = n * n + 1 := by
  rw [primeCounting_eq_oddPrimePrefix_add_one (poolMaximum_prime n).two_le,
    oddPrimePrefix_poolMaximum_card]

/-- Exact discrete partial summation in terms of mathlib's usual prime-count
function, with the contribution of 2 removed at precisely the right integer
endpoints. -/
theorem oddPrimePool_total_primeCounting_identity (n : ℕ) :
    (Lucas.poolTotal n : ℝ) +
      ∑ k ∈ Finset.range (poolMaximum n),
        ((Nat.primeCounting k : ℝ) - (if 2 ≤ k then 1 else 0)) =
          ((n * n : ℕ) : ℝ) * (poolMaximum n : ℝ) := by
  have h := oddPrimePool_total_count_identity n
  simp_rw [oddPrimePrefix_card_real_eq_primeCounting] at h
  exact h

end
end Sude
