import Sude.FWAffineWheelIntervalCounts

/-! Arithmetic for the AW1 wheel extension. The discrepancy premise is
retained; see `problems/prime-line-sums/manuscripts/
cutoff2_affine_wheel_prefix.md`, AW1. -/
namespace Sude
noncomputable section

/-- The number of p-multiples in `(a,a+K]` differs from K/p by less than one,
including intervals of length zero. -/
theorem fw_multiple_interval_count_error (a K p : ℕ) (hp : 0 < p) :
    let M := (a + K) / p - a / p
    (K : ℝ) / p - 1 < (M : ℝ) ∧ (M : ℝ) < (K : ℝ) / p + 1 := by
  dsimp only
  have hle : a / p ≤ (a + K) / p := Nat.div_le_div_right (by omega)
  have hmodA := Nat.mod_add_div a p
  have hmodB := Nat.mod_add_div (a + K) p
  have ha := Nat.mod_lt a hp
  have hb := Nat.mod_lt (a + K) hp
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hAr : (((a % p : ℕ) : ℝ) + (p : ℝ) * (a / p : ℕ)) = a := by exact_mod_cast hmodA
  have hBr : (((((a + K) % p : ℕ) : ℝ)) + (p : ℝ) * ((a + K) / p : ℕ)) = (a : ℝ) + K := by exact_mod_cast hmodB
  have har : ((a % p : ℕ) : ℝ) < p := by exact_mod_cast ha
  have hbr : (((a + K) % p : ℕ) : ℝ) < p := by exact_mod_cast hb
  have hmA : (0 : ℝ) ≤ (a % p : ℕ) := by positivity
  have hmB : (0 : ℝ) ≤ ((a + K) % p : ℕ) := by positivity
  have hM : (((a + K) / p - a / p : ℕ) : ℝ) =
      (((a + K) / p : ℕ) : ℝ) - (a / p : ℕ) := by exact Nat.cast_sub hle
  have hdiv : ((K : ℝ) / p) * p = K := div_mul_cancel₀ _ (ne_of_gt hpr)
  constructor <;> rw [hM] <;> nlinarith

/-- The real arithmetic behind AW1, independently of the unit-count
bijection. Both discrepancies and the p-multiple rounding are explicit. -/
theorem fw_affine_extension_real_bound (K M p rho C u v w : ℝ)
    (hrho : 0 ≤ rho)
    (hMlo : K / p - 1 ≤ M) (hMhi : M ≤ K / p + 1)
    (huLo : rho * K - C ≤ u) (huHi : u ≤ rho * K + C)
    (hvLo : rho * M - C ≤ v) (hvHi : v ≤ rho * M + C)
    (hsplit : w + v = u) :
    ((1 - 1 / p) * rho) * K - (2 * C + rho) ≤ w ∧
      w ≤ ((1 - 1 / p) * rho) * K + (2 * C + rho) := by
  have hlo := mul_le_mul_of_nonneg_left hMlo hrho
  have hhi := mul_le_mul_of_nonneg_left hMhi hrho
  ring_nf at hlo hhi ⊢
  constructor <;> nlinarith

/-- Uniform two-sided discrepancy on all natural intervals `(a,a+K]`.
No assumption that these values have been certified is built in. -/
def FWAffineIntervalDiscrepancy (W : ℕ) (rho C : ℝ) : Prop :=
  ∀ a K : ℕ,
    rho * K - C ≤ ((fwIntervalUnits W a K).card : ℝ) ∧
    ((fwIntervalUnits W a K).card : ℝ) ≤ rho * K + C

/-- AW1: adjoining a prime not dividing W updates the density parameter and
the two-sided error to `(1-1/p)*rho` and `2*C+rho`. All interval endpoints,
including K=0, are covered. -/
theorem fw_affine_interval_discrepancy_extend
    (W p : ℕ) (rho C : ℝ) (hp : Nat.Prime p) (hnotdvd : ¬ p ∣ W)
    (hrho : 0 ≤ rho) (hdisc : FWAffineIntervalDiscrepancy W rho C) :
    FWAffineIntervalDiscrepancy (W * p) ((1 - 1 / (p : ℝ)) * rho) (2 * C + rho) := by
  intro a K
  let M := (a + K) / p - a / p
  have hm := fw_multiple_interval_count_error a K p hp.pos
  have hu := hdisc a K
  have hv := hdisc (a / p) M
  have hsplit := fw_interval_units_prime_extension W p a K hp
    (hp.coprime_iff_not_dvd.mpr hnotdvd)
  have hsplitR : ((fwIntervalUnits (W * p) a K).card : ℝ) +
      ((fwIntervalUnits W (a / p) M).card : ℝ) =
      ((fwIntervalUnits W a K).card : ℝ) := by exact_mod_cast hsplit
  exact fw_affine_extension_real_bound K M p rho C
    ((fwIntervalUnits W a K).card : ℝ)
    ((fwIntervalUnits W (a / p) M).card : ℝ)
    ((fwIntervalUnits (W * p) a K).card : ℝ)
    hrho hm.1.le hm.2.le hu.1 hu.2 hv.1 hv.2 hsplitR

/-- A two-sided interval certificate supplies the one-sided hypothesis used
by the AW2 short-neighbor theorem. -/
theorem fw_affine_interval_discrepancy_implies_window (W : ℕ) (rho C : ℝ)
    (hdisc : FWAffineIntervalDiscrepancy W rho C) :
    FWAffineWheelDiscrepancy W rho C :=
  fw_interval_upper_implies_affine_discrepancy W rho C (fun a K => (hdisc a K).2)

/-- The empty wheel is an exact initial interval certificate. -/
theorem fw_affine_interval_discrepancy_one : FWAffineIntervalDiscrepancy 1 1 0 := by
  intro a K
  simp [fwIntervalUnits, Nat.card_Ioc]

end
end Sude
