import Sude.FWAffineBaseCertificate
import Sude.FWMixedWheelUnits

/-! Exact AW1 discrepancies for the eight affine wheels used by the frozen
FW recipe. The base period is certified in `FWAffineBaseCertificate`;
these bounds do not prove the recipe's numeric gates or trace existence.
Source: `problems/prime-line-sums/code/cutoff2_affine_wheel_prefix.py`,
`wheel_record`, and `inputs/cutoff2_controller_far_wide_inputs.json`. -/
namespace Sude
noncomputable section

/-- Exact AW1 densities, in frozen affine-stage order. -/
def fwMixedWheelRho (i : Fin 8) : ℝ := ![
  6144 / 17017,
  110592 / 323323,
  221184 / 676039,
  884736 / 2800733,
  26542080 / 86822723,
  955514880 / 3212440751,
  38220595200 / 131710070791,
  1605264998400 / 5663533044013 ] i

/-- Exact AW1 discrepancy constants, in frozen affine-stage order. -/
def fwMixedWheelError (i : Fin 8) : ℝ := ![
  13820 / 1001,
  476024 / 17017,
  18199504 / 323323,
  839610208 / 7436429,
  150976832 / 667667,
  3025505777792 / 6685349671,
  7722793179392 / 8529584063,
  1412903474340352 / 780128880839 ] i

theorem fw_mixed_wheel_discrepancy_0 :
    FWAffineIntervalDiscrepancy 255255 (6144 / 17017 : ℝ) (13820 / 1001 : ℝ) :=
  fw_first_affine_wheel_interval_discrepancy

theorem fw_mixed_wheel_discrepancy_1 :
    FWAffineIntervalDiscrepancy 4849845 (110592 / 323323 : ℝ) (476024 / 17017 : ℝ) := by
  have hh := fw_affine_interval_discrepancy_extend 255255 19 (6144 / 17017) (13820 / 1001)
    (by norm_num) (by decide) (by norm_num) fw_mixed_wheel_discrepancy_0
  norm_num at hh
  exact hh

theorem fw_mixed_wheel_discrepancy_2 :
    FWAffineIntervalDiscrepancy 111546435 (221184 / 676039 : ℝ) (18199504 / 323323 : ℝ) := by
  have hh := fw_affine_interval_discrepancy_extend 4849845 23 (110592 / 323323) (476024 / 17017)
    (by norm_num) (by decide) (by norm_num) fw_mixed_wheel_discrepancy_1
  norm_num at hh
  exact hh

theorem fw_mixed_wheel_discrepancy_3 :
    FWAffineIntervalDiscrepancy 3234846615 (884736 / 2800733 : ℝ) (839610208 / 7436429 : ℝ) := by
  have hh := fw_affine_interval_discrepancy_extend 111546435 29 (221184 / 676039) (18199504 / 323323)
    (by norm_num) (by decide) (by norm_num) fw_mixed_wheel_discrepancy_2
  norm_num at hh
  exact hh

theorem fw_mixed_wheel_discrepancy_4 :
    FWAffineIntervalDiscrepancy 100280245065 (26542080 / 86822723 : ℝ) (150976832 / 667667 : ℝ) := by
  have hh := fw_affine_interval_discrepancy_extend 3234846615 31 (884736 / 2800733) (839610208 / 7436429)
    (by norm_num) (by decide) (by norm_num) fw_mixed_wheel_discrepancy_3
  norm_num at hh
  exact hh

theorem fw_mixed_wheel_discrepancy_5 :
    FWAffineIntervalDiscrepancy 3710369067405 (955514880 / 3212440751 : ℝ) (3025505777792 / 6685349671 : ℝ) := by
  have hh := fw_affine_interval_discrepancy_extend 100280245065 37 (26542080 / 86822723) (150976832 / 667667)
    (by norm_num) (by decide) (by norm_num) fw_mixed_wheel_discrepancy_4
  norm_num at hh
  exact hh

theorem fw_mixed_wheel_discrepancy_6 :
    FWAffineIntervalDiscrepancy 152125131763605 (38220595200 / 131710070791 : ℝ) (7722793179392 / 8529584063 : ℝ) := by
  have hh := fw_affine_interval_discrepancy_extend 3710369067405 41 (955514880 / 3212440751) (3025505777792 / 6685349671)
    (by norm_num) (by decide) (by norm_num) fw_mixed_wheel_discrepancy_5
  norm_num at hh
  exact hh

theorem fw_mixed_wheel_discrepancy_7 :
    FWAffineIntervalDiscrepancy 6541380665835015 (1605264998400 / 5663533044013 : ℝ) (1412903474340352 / 780128880839 : ℝ) := by
  have hh := fw_affine_interval_discrepancy_extend 152125131763605 43 (38220595200 / 131710070791) (7722793179392 / 8529584063)
    (by norm_num) (by decide) (by norm_num) fw_mixed_wheel_discrepancy_6
  norm_num at hh
  exact hh

/-- Every source wheel has its exact source density and the AW1 error bound,
uniformly for every natural interval. -/
theorem fw_mixed_wheel_interval_discrepancy (i : Fin 8) :
    FWAffineIntervalDiscrepancy (fwMixedWheel i) (fwMixedWheelRho i) (fwMixedWheelError i) := by
  fin_cases i
  · simpa [fwMixedWheel, fwMixedWheelFactors, fwMixedWheelRho, fwMixedWheelError] using fw_mixed_wheel_discrepancy_0
  · simpa [fwMixedWheel, fwMixedWheelFactors, fwMixedWheelRho, fwMixedWheelError] using fw_mixed_wheel_discrepancy_1
  · simpa [fwMixedWheel, fwMixedWheelFactors, fwMixedWheelRho, fwMixedWheelError] using fw_mixed_wheel_discrepancy_2
  · simpa [fwMixedWheel, fwMixedWheelFactors, fwMixedWheelRho, fwMixedWheelError] using fw_mixed_wheel_discrepancy_3
  · simpa [fwMixedWheel, fwMixedWheelFactors, fwMixedWheelRho, fwMixedWheelError] using fw_mixed_wheel_discrepancy_4
  · simpa [fwMixedWheel, fwMixedWheelFactors, fwMixedWheelRho, fwMixedWheelError] using fw_mixed_wheel_discrepancy_5
  · simpa [fwMixedWheel, fwMixedWheelFactors, fwMixedWheelRho, fwMixedWheelError] using fw_mixed_wheel_discrepancy_6
  · simpa [fwMixedWheel, fwMixedWheelFactors, fwMixedWheelRho, fwMixedWheelError] using fw_mixed_wheel_discrepancy_7

/-- The same certificates provide the upper discrepancy interface consumed
by the conditional AW2 short-neighbor bound. -/
theorem fw_mixed_wheel_affine_discrepancy (i : Fin 8) :
    FWAffineWheelDiscrepancy (fwMixedWheel i) (fwMixedWheelRho i) (fwMixedWheelError i) :=
  fw_affine_interval_discrepancy_implies_window _ _ _ (fw_mixed_wheel_interval_discrepancy i)

theorem fw_mixed_wheel_rho_pos (i : Fin 8) : 0 < fwMixedWheelRho i := by
  fin_cases i <;> norm_num [fwMixedWheelRho]

/-- The source affine short-pair charge for any screened pool subset. This
does not supply a population of pairs or an admissible growth threshold. -/
theorem fw_mixed_wheel_screened_affine_short_pair_count (i : Fin 8) {n : ℕ}
    (S : Finset ℕ) (P : Finset (ℕ × ℕ)) (D : ℝ) (hne : S.Nonempty)
    (hS : S ⊆ (poolFinset n).filter (fun p => 43 < p))
    (hP : ∀ z ∈ P, z.1 ∈ S ∧ z.2 ∈ S ∧ z.1 < z.2 ∧ z.2 % 2 = z.1 % 2)
    (hD : 0 < D) :
    (((P.filter fun z => ((z.2 - z.1 : ℕ) : ℝ) < D).card : ℝ)) <
      (S.card : ℝ) * (fwMixedWheelRho i * D / 2 + fwMixedWheelError i) := by
  apply fw_affine_short_pair_count S P (fwMixedWheel i) D (fwMixedWheelRho i)
    (fwMixedWheelError i) hne (fw_mixed_wheel_pos_odd i).2 ?_ hP hD
    (fw_mixed_wheel_rho_pos i) (fw_mixed_wheel_affine_discrepancy i)
  intro p hp
  have hp' := fw_screened_pool_mixed_wheel_units hS p hp
  exact ⟨hp'.2.2.1, hp'.2.2.2 i⟩

end
end Sude
