import Sude.FC2KExpansionGate
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen

/-! Curvature of the finite controller's cut entropy. -/
namespace Sude

/-- The actual FC2K constants make the source's displayed curvature strictly
positive all the way to one half. -/
theorem fc2k_curvature_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    0 < (2 - (3 * ((199 : ℝ) / 1200)) /
      (1 - (1 + (199 : ℝ) / 1200) * t)) / (t * (1 - t)) := by
  have hd : 0 < 1 - (1 + (199 : ℝ) / 1200) * t := by linarith
  have hn : 0 < 2 - (3 * ((199 : ℝ) / 1200)) /
      (1 - (1 + (199 : ℝ) / 1200) * t) := by
    apply sub_pos.mpr
    apply (div_lt_iff₀ hd).mpr
    linarith
  exact div_pos hn (mul_pos ht0 (by linarith))

noncomputable def fc2kEntropySlope (t : ℝ) : ℝ :=
  let a : ℝ := 199 / 1200
  let z := a * t / (1 - t)
  3 * (Real.binEntropy a - Real.binEntropy z +
    a / (1 - t) * (Real.log (1 - z) - Real.log z)) -
    2 * (Real.log (1 - t) - Real.log t)

/-- The derivative is computed on the full domain needed by FC2K. -/
theorem fc2k_entropy_hasDerivAt {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    HasDerivAt fc2kCutEntropy (fc2kEntropySlope t) t := by
  let a : ℝ := 199 / 1200
  let z : ℝ := a * t / (1 - t)
  have hden : 1 - t ≠ 0 := by linarith
  have hzpos : 0 < z := by
    dsimp [z, a]
    exact div_pos (mul_pos (by norm_num) ht0) (by linarith)
  have hzlt : z < 1 := by
    dsimp [z, a]
    apply (div_lt_one (by linarith : 0 < 1 - t)).2
    linarith
  have hz : HasDerivAt (fun x : ℝ => a * x / (1 - x)) (a / (1 - t)^2) t := by
    have h := ((hasDerivAt_const t a).mul (hasDerivAt_id t)).div
      ((hasDerivAt_const t 1).sub (hasDerivAt_id t)) hden
    convert h using 1 <;> try rfl
    simp only [Pi.sub_apply, Pi.mul_apply, id_eq, zero_mul, zero_sub, zero_add, mul_one]
    congr 1
    ring
  have hE := (Real.hasDerivAt_binEntropy (ne_of_gt hzpos) (ne_of_lt hzlt)).comp t hz
  have hT := Real.hasDerivAt_binEntropy (ne_of_gt ht0) (by linarith : t ≠ 1)
  have hf := (((hasDerivAt_id t).mul_const (Real.binEntropy a)).add
    (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).mul hE)).const_mul 3 |>.sub
      (hT.const_mul 2)
  change HasDerivAt fc2kCutEntropy (fc2kEntropySlope t) t
  convert hf using 1 <;> try rfl
  dsimp [fc2kEntropySlope, z, a, Function.comp_def]
  field_simp [hden]
  ring

/-- The source's curvature formula is the derivative of the proved slope. -/
theorem fc2k_entropySlope_hasDerivAt {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    HasDerivAt fc2kEntropySlope
      ((2 - (3 * ((199 : ℝ) / 1200)) /
        (1 - (1 + (199 : ℝ) / 1200) * t)) / (t * (1 - t))) t := by
  let a : ℝ := 199 / 1200
  let z : ℝ := a * t / (1 - t)
  have hden : 1 - t ≠ 0 := by linarith
  have hzpos : 0 < z := by
    dsimp [z, a]
    exact div_pos (mul_pos (by norm_num) ht0) (by linarith)
  have hzlt : z < 1 := by
    dsimp [z, a]
    apply (div_lt_one (by linarith : 0 < 1 - t)).2
    linarith
  have hz : HasDerivAt (fun x : ℝ => a * x / (1 - x)) (a / (1 - t)^2) t := by
    have h := ((hasDerivAt_const t a).mul (hasDerivAt_id t)).div
      ((hasDerivAt_const t 1).sub (hasDerivAt_id t)) hden
    convert h using 1 <;> try rfl
    simp only [Pi.sub_apply, Pi.mul_apply, id_eq, zero_mul, zero_sub, zero_add, mul_one]
    congr 1
    ring
  have hw : HasDerivAt (fun x : ℝ => a / (1 - x)) (a / (1 - t)^2) t := by
    have h := (hasDerivAt_const t a).div
      ((hasDerivAt_const t 1).sub (hasDerivAt_id t)) hden
    convert h using 1 <;> try rfl
    simp only [Pi.sub_apply, id_eq, zero_mul, zero_sub]
    ring
  have hE := (Real.hasDerivAt_binEntropy (ne_of_gt hzpos) (ne_of_lt hzlt)).comp t hz
  have hlogz := hz.log (ne_of_gt hzpos)
  have hlogone := ((hasDerivAt_const t 1).sub hz).log (by linarith : 1 - z ≠ 0)
  have hlogt := (hasDerivAt_id t).log (ne_of_gt ht0)
  have hlogt1 := ((hasDerivAt_const t 1).sub (hasDerivAt_id t)).log hden
  have hf := ((((hasDerivAt_const t (Real.binEntropy a)).sub hE).add
    (hw.mul (hlogone.sub hlogz))).const_mul 3).sub ((hlogt1.sub hlogt).const_mul 2)
  convert hf using 1 <;> try rfl
  dsimp [fc2kEntropySlope, z, a, Function.comp_def] at *
  field_simp [hden, ne_of_gt ht0, show (1 - (1 + (199 : ℝ) / 1200) * t) ≠ 0 by linarith]
  ring_nf
  have hnormal : (1200 : ℝ) - t * 1399 ≠ 0 := by linarith
  field_simp [hnormal]
  ring

/-- For FC2K's particular parameters the cut-entropy function is convex
on the entire large-cut interval. -/
theorem fc2k_entropy_convex :
    ConvexOn ℝ (Set.Icc ((1 : ℝ) / 256) (1 / 2)) fc2kCutEntropy := by
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (f' := fc2kEntropySlope)
    (f'' := fun t => (2 - (3 * ((199 : ℝ) / 1200)) /
      (1 - (1 + (199 : ℝ) / 1200) * t)) / (t * (1 - t)))
    (convex_Icc _ _)
  · intro x hx
    exact (fc2k_entropy_hasDerivAt (by linarith [hx.1]) hx.2).continuousAt.continuousWithinAt
  · intro x hx
    have hx' := interior_subset hx
    exact (fc2k_entropy_hasDerivAt (by linarith [hx'.1]) hx'.2).hasDerivWithinAt
  · intro x hx
    have hx' := interior_subset hx
    exact (fc2k_entropySlope_hasDerivAt (by linarith [hx'.1]) hx'.2).hasDerivWithinAt
  · intro x hx
    have hx' := interior_subset hx
    exact (fc2k_curvature_pos (by linarith [hx'.1]) hx'.2).le

/-- The endpoint certificates therefore bound the actual entropy for every
real cut fraction in the full large-cut interval. -/
theorem fc2k_entropy_interval_gate {t : ℝ} (ht0 : 1 / 256 ≤ t) (ht1 : t ≤ 1 / 2) :
    fc2kCutEntropy t < -(1 : ℝ) / 34 := by
  have hmax := fc2k_entropy_convex.le_max_of_mem_Icc
    (show (1 : ℝ) / 256 ∈ Set.Icc (1 / 256) (1 / 2) by norm_num)
    (show (1 : ℝ) / 2 ∈ Set.Icc (1 / 256) (1 / 2) by norm_num)
    ⟨ht0, ht1⟩
  exact lt_of_le_of_lt hmax (max_lt fc2k_entropy_small_gate fc2k_entropy_half_gate)

end Sude
