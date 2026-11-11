import Sude.FWAffinePeriodicCriterion
import Sude.FWBaseWheelPrefix
/-! Exact FW base and first affine-wheel discrepancy certificates.
Source: `problems/prime-line-sums/code/cutoff2_affine_wheel_prefix.py`,
`exact_period` and `wheel_record`; see also AW1 in the corresponding manuscript.
No stage numerical gates or trace construction are asserted. -/
namespace Sude
noncomputable section
private theorem base_data : fwPeriodPrefix 15015 15015 = 5760 ∧
 ∀ r ≤ 15015, 5760 * r ≤ 15015 * fwPeriodPrefix 15015 r + 47505 ∧
   15015 * fwPeriodPrefix 15015 r ≤ 5760 * r + 53265 := by
  obtain ⟨htotal, hbounds⟩ := fw_base_prefix_full_certificate
  refine ⟨?_, ?_⟩
  · simpa [fwPeriodPrefix, fwBaseWheelPrefix] using htotal
  · intro r hr
    simpa [fwPeriodPrefix, fwBaseWheelPrefix, fwBasePrefixBounds] using hbounds r hr

theorem fw_base_wheel_totient : Nat.totient 15015 = 5760 := by
  have h := fw_period_prefix_add_period 15015 0
  simp [fwPeriodPrefix] at h
  rw [← h]
  exact base_data.1

theorem fw_base_wheel_interval_discrepancy : FWAffineIntervalDiscrepancy 15015 (384 / 1001 : ℝ) (6718 / 1001 : ℝ) := by
  have hb : ∀ r < 15015, (-47505 : ℤ) ≤ fwPeriodPrefixError 15015 r ∧
      fwPeriodPrefixError 15015 r ≤ 53265 := by
    intro r hr
    have hs := base_data.2 r (by omega)
    unfold fwPeriodPrefixError
    rw [fw_base_wheel_totient]
    constructor <;> omega
  have hh := fw_affine_interval_discrepancy_of_prefix_bounds 15015 (by decide)
    (-47505) 53265 hb
  rw [fw_base_wheel_totient] at hh
  norm_num at hh
  exact hh

theorem fw_first_affine_wheel_interval_discrepancy : FWAffineIntervalDiscrepancy 255255 (6144 / 17017 : ℝ) (13820 / 1001 : ℝ) := by
  have hh := fw_affine_interval_discrepancy_extend 15015 17 (384/1001) (6718/1001)
    (by norm_num) (by decide) (by norm_num) fw_base_wheel_interval_discrepancy
  norm_num at hh
  exact hh
end
end Sude
