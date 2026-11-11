import Sude.FWEighthAffinePhase

/-! Indexed fixed-mass origin gates for the eight source affine wheels.
The displayed bounds are existing proved envelopes; this module does not
construct a radius, trace, any phase, or a target crossing. -/
namespace Sude
noncomputable section

/-- Integer upper bounds on the eight source wheel origins, in recipe order. -/
def fwAffineOriginUpper (i : Fin 8) : ℕ :=
  ![1108, 2196, 4380, 8747, 17479, 34942, 69868, 139718] i

/-- The fixed normalized terminal mass pays every listed wheel-origin bound.
The positivity of X and the lower bound on mf remain explicit. -/
theorem fw_indexed_affine_origin_lt_upper (i : Fin 8) {X mf : ℝ}
    (hX : 0 < X) (hmf : (3257 / 100000 : ℝ) ≤ mf) :
    fwAffineOrigin (fwMixedWheelError i) 1 X (3981035 / 10000000) (mf * X) <
      (fwAffineOriginUpper i : ℝ) := by
  fin_cases i
  · simpa [fwAffineOriginUpper] using fw_first_affine_origin_lt_1108 hX hmf
  · simpa [fwAffineOriginUpper] using fw_second_affine_origin_lt_2196 hX hmf
  · simpa [fwAffineOriginUpper] using fw_third_affine_origin_lt_4380 hX hmf
  · simpa [fwAffineOriginUpper] using fw_fourth_affine_origin_lt_8747 hX hmf
  · simpa [fwAffineOriginUpper] using fw_fifth_affine_origin_lt_17479 hX hmf
  · simpa [fwAffineOriginUpper] using fw_sixth_affine_origin_lt_34942 hX hmf
  · simpa [fwAffineOriginUpper] using fw_seventh_affine_origin_lt_69868 hX hmf
  · simpa [fwAffineOriginUpper] using fw_eighth_affine_origin_lt_139718 hX hmf

/-- An actual or certified radius at least the indexed integer bound clears
that wheel's strictly positive origin-shift gate. -/
theorem fw_indexed_affine_shift_of_radius (i : Fin 8) {X mf : ℝ} {R : ℕ}
    (hX : 0 < X) (hmf : (3257 / 100000 : ℝ) ≤ mf)
    (hR : fwAffineOriginUpper i ≤ R) :
    0 < (R : ℝ) -
      fwAffineOrigin (fwMixedWheelError i) 1 X (3981035 / 10000000) (mf * X) := by
  have ho := fw_indexed_affine_origin_lt_upper i hX hmf
  have hR' : (fwAffineOriginUpper i : ℝ) ≤ R := by exact_mod_cast hR
  linarith

end
end Sude
