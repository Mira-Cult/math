import Sude.LiBGPropagation

/-! Explicit growth of the BG comparison gaps on `[x/2,x]`. The estimates
are elementary consequences of the existing derivatives and use no bounds
at any base point. -/

namespace Sude
noncomputable section

private theorem half_log_geometry {x : ℝ} (hx : 2 ≤ x)
    (hu : 22 ≤ Real.log x) :
    2 ≤ x / 2 ∧ ∀ t ∈ Set.Icc (x / 2) x,
      2 ≤ t ∧ 12 ≤ Real.log t ∧ Real.log t ≤ Real.log x := by
  have hxpos : 0 < x := by linarith
  have hexp : Real.exp 22 ≤ x := by
    have h := Real.exp_le_exp.mpr hu
    simpa [Real.exp_log hxpos] using h
  have hxhalf : 2 ≤ x / 2 := by
    have h := Real.add_one_le_exp (22 : ℝ)
    linarith
  refine ⟨hxhalf, ?_⟩
  intro t ht
  have ht2 : 2 ≤ t := le_trans hxhalf ht.1
  have hlogupper := Real.log_le_log (by linarith : 0 < t) ht.2
  have hloglower := Real.log_le_log (by linarith : 0 < x / 2) ht.1
  rw [Real.log_div (ne_of_gt hxpos) (by norm_num : (2 : ℝ) ≠ 0)] at hloglower
  have hlogtwo := Real.log_two_lt_d9
  exact ⟨ht2, by linarith, hlogupper⟩

private theorem gap_growth_on_half {x c : ℝ} (hx : 2 ≤ x / 2)
    {f : ℝ → ℝ} (hder : ∀ t, 2 ≤ t → DifferentiableAt ℝ f t)
    (hbound : ∀ t ∈ Set.Icc (x / 2) x, c ≤ deriv f t) :
    c * (x / 2) ≤ f x - f (x / 2) := by
  have hxpos : 0 ≤ x := by linarith
  have hcont : ContinuousOn f (Set.Icc (x / 2) x) := by
    intro t ht
    exact (hder t (le_trans hx ht.1)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Set.Icc (x / 2) x)) := by
    intro t ht
    have ht' := interior_subset ht
    exact (hder t (le_trans hx ht'.1)).differentiableWithinAt
  have hb : ∀ t ∈ interior (Set.Icc (x / 2) x), c ≤ deriv f t := by
    intro t ht
    exact hbound t (interior_subset ht)
  have hh := (convex_Icc (x / 2) x).mul_sub_le_image_sub_of_le_deriv
    hcont hdiff hb (x / 2) ⟨le_rfl, by linarith⟩ x ⟨by linarith, le_rfl⟩ (by linarith)
  convert hh using 1; ring

/-- The lower-comparison gap grows by at least `12*x/(log x)^5` from
`x/2` to `x` on the stated positive logarithmic domain. -/
theorem bgLiLower_gap_half_growth {x : ℝ} (hx : 2 ≤ x)
    (hu : 22 ≤ Real.log x) :
    12 * x / (Real.log x)^5 ≤
      (liFromTwo x - bgLiLower x) - (liFromTwo (x / 2) - bgLiLower (x / 2)) := by
  obtain ⟨hhalf, hgeom⟩ := half_log_geometry hx hu
  have hder (t : ℝ) (ht : 2 ≤ t) :
      DifferentiableAt ℝ (fun t => liFromTwo t - bgLiLower t) t :=
    (bgLiLower_gap_deriv ht).differentiableAt
  have hbound : ∀ t ∈ Set.Icc (x / 2) x,
      24 / (Real.log x)^5 ≤ deriv (fun t => liFromTwo t - bgLiLower t) t := by
    intro t ht
    obtain ⟨ht2, htlog, htupper⟩ := hgeom t ht
    rw [(bgLiLower_gap_deriv ht2).deriv]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact pow_le_pow_left₀ (by linarith) htupper 5
  have hg := gap_growth_on_half hhalf hder hbound
  convert hg using 1; ring

/-- The upper-comparison gap grows by at least `x/(2*(log x)^3)` from
`x/2` to `x` on the stated positive logarithmic domain. -/
theorem bgLiUpper_gap_half_growth {x : ℝ} (hx : 2 ≤ x)
    (hu : 22 ≤ Real.log x) :
    x / (2 * (Real.log x)^3) ≤
      (bgLiUpper x - liFromTwo x) - (bgLiUpper (x / 2) - liFromTwo (x / 2)) := by
  obtain ⟨hhalf, hgeom⟩ := half_log_geometry hx hu
  have hder (t : ℝ) (ht : 2 ≤ t) :
      DifferentiableAt ℝ (fun t => bgLiUpper t - liFromTwo t) t :=
    (bgLiUpper_gap_deriv ht).differentiableAt
  have hbound : ∀ t ∈ Set.Icc (x / 2) x,
      1 / (Real.log x)^3 ≤ deriv (fun t => bgLiUpper t - liFromTwo t) t := by
    intro t ht
    obtain ⟨ht2, htlog, htupper⟩ := hgeom t ht
    rw [(bgLiUpper_gap_deriv ht2).deriv]
    have hvpos : 0 < Real.log t := by linarith
    have hp : (Real.log t)^3 ≤ (Real.log x)^3 :=
      pow_le_pow_left₀ hvpos.le htupper 3
    have hfirst : 1 / (Real.log x)^3 ≤ 1 / (Real.log t)^3 :=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos hvpos 3) hp
    have hsecond : 1 / (Real.log t)^3 ≤ (2 * Real.log t - 12) / (Real.log t)^4 := by
      apply (div_le_div_iff₀ (pow_pos hvpos 3) (pow_pos hvpos 4)).2
      have hz : 0 ≤ (Real.log t - 12) * (Real.log t)^3 :=
        mul_nonneg (by linarith) (pow_nonneg hvpos.le 3)
      nlinarith [hz]
    exact hfirst.trans hsecond
  have hg := gap_growth_on_half hhalf hder hbound
  convert hg using 1; ring

end
end Sude
