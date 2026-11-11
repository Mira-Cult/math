import Sude.GlobalPoolMeanBounds
import Sude.OddCountUniformTheta
import Sude.OddCountCorrelatedMean
import Sude.FWMeanCellTransport

/-!
# Tight Prescribed-Pool Mean Bounds on `[2001, 19483]`

Extends the unconditional BG logarithmic-integral comparisons (`bgLiLower x < liFromTwo x < bgLiUpper x`),
the finite-theta aggregate odd-prime count bound, and the correlated pool-mean identity down to
`65170000 ≤ X` (covering every order `n ≥ 2001`), and establishes the tight normalized mean
enclosure `959 / 2000 < m / X < 491 / 1000` (`0.4795 < m / X < 0.4910`) throughout
`2001 ≤ n ≤ 19483`.
-/

namespace Sude

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem log_65170000_bounds :
    (1799 / 100 : ℝ) < Real.log (65170000 : ℝ) ∧
    Real.log (65170000 : ℝ) < 18 := by
  constructor
  · have hpow : (2 : ℝ) ^ 597 < (65170000 : ℝ) ^ 23 := by
      exact_mod_cast (by decide +kernel : (2 : ℕ) ^ 597 < 65170000 ^ 23)
    have hlog := Real.log_lt_log (by positivity) hpow
    rw [Real.log_pow, Real.log_pow] at hlog
    have hln2 := Real.log_two_gt_d9
    push_cast at hlog
    linarith
  · have he1 : (2718281827 / 1000000000 : ℝ) < Real.exp 1 := by
      linarith [Real.exp_one_gt_d9]
    have hnum : (65170000 : ℝ) < (2718281827 / 1000000000 : ℝ) ^ 18 := by norm_num
    have hp : (2718281827 / 1000000000 : ℝ) ^ 18 < (Real.exp 1) ^ 18 :=
      pow_lt_pow_left₀ he1 (by positivity) (by norm_num)
    have hexp18 : (Real.exp 1) ^ 18 = Real.exp (18 : ℝ) := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [hexp18] at hp
    have hlt : (65170000 : ℝ) < Real.exp (18 : ℝ) := hnum.trans hp
    have hlog := Real.log_lt_log (by norm_num) hlt
    rwa [Real.log_exp] at hlog

private theorem half_log_geometry_65170000 {x : ℝ} (hx : (65170000 : ℝ) ≤ x) :
    2 ≤ x / 2 ∧ ∀ t ∈ Set.Icc (x / 2) x,
      2 ≤ t ∧ 12 ≤ Real.log t ∧ Real.log t ≤ Real.log x := by
  have hxpos : 0 < x := by linarith
  have hxhalf : 2 ≤ x / 2 := by linarith
  have hlogx : (1799 / 100 : ℝ) < Real.log x :=
    lt_of_lt_of_le log_65170000_bounds.1 (Real.log_le_log (by norm_num) hx)
  refine ⟨hxhalf, ?_⟩
  intro t ht
  have ht2 : 2 ≤ t := le_trans hxhalf ht.1
  have hlogupper := Real.log_le_log (by linarith : 0 < t) ht.2
  have hloglower := Real.log_le_log (by linarith : 0 < x / 2) ht.1
  rw [Real.log_div (ne_of_gt hxpos) (by norm_num : (2 : ℝ) ≠ 0)] at hloglower
  have hlogtwo := Real.log_two_lt_d9
  exact ⟨ht2, by linarith, hlogupper⟩

private theorem gap_growth_on_half_local {x c : ℝ} (hx : 2 ≤ x / 2)
    {f : ℝ → ℝ} (hder : ∀ t, 2 ≤ t → DifferentiableAt ℝ f t)
    (hbound : ∀ t ∈ Set.Icc (x / 2) x, c ≤ deriv f t) :
    c * (x / 2) ≤ f x - f (x / 2) := by
  have hcont : ContinuousOn f (Set.Icc (x / 2) x) := fun t ht =>
    (hder t (le_trans hx ht.1)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Set.Icc (x / 2) x)) := fun t ht =>
    (hder t (le_trans hx (interior_subset ht).1)).differentiableWithinAt
  have hb : ∀ t ∈ interior (Set.Icc (x / 2) x), c ≤ deriv f t := fun t ht =>
    hbound t (interior_subset ht)
  have hh := (convex_Icc (x / 2) x).mul_sub_le_image_sub_of_le_deriv
    hcont hdiff hb (x / 2) ⟨le_rfl, by linarith⟩ x ⟨by linarith, le_rfl⟩ (by linarith)
  convert hh using 1
  ring

/-- Unconditional BG logarithmic-integral bounds for all `x ≥ 65170000`. -/
theorem bg_li_bounds_of_ge_65170000 {x : ℝ} (hx : (65170000 : ℝ) ≤ x) :
    bgLiLower x < liFromTwo x ∧ liFromTwo x < bgLiUpper x := by
  by_cases hu22 : 22 ≤ Real.log x
  · exact bg_li_bounds_of_log_ge_22 (by linarith) hu22
  · have hu_lt : Real.log x < 22 := lt_of_not_ge hu22
    have hxpos : 0 < x := by linarith
    have hhalfpos : 0 < x / 2 := by linarith
    have hu_lo : (1799 / 100 : ℝ) < Real.log x :=
      lt_of_lt_of_le log_65170000_bounds.1 (Real.log_le_log (by norm_num) hx)
    have hloghalf : 6 ≤ Real.log (x / 2) := by
      rw [Real.log_div (ne_of_gt hxpos) (by norm_num : (2 : ℝ) ≠ 0)]
      linarith [Real.log_two_lt_d9]
    have hhalf : Real.exp 6 ≤ x / 2 := by
      have h := Real.exp_le_exp.mpr hloghalf
      simpa [Real.exp_log hhalfpos] using h
    have he : (2 : ℝ) ≤ Real.exp 6 := by linarith [Real.add_one_le_exp (6 : ℝ)]
    have hhalf2 : 2 ≤ x / 2 := he.trans hhalf
    have hmonoL := bg_lower_gap_monotone (show (2 : ℝ) ∈ Set.Ici 2 by simp) hhalf2 hhalf2
    have hmonoU := bg_upper_gap_monotone (show Real.exp 6 ∈ Set.Ici (Real.exp 6) by simp) hhalf hhalf
    have hbaseL := bg_lower_gap_at_two_gt
    have hbaseU := bg_upper_gap_at_exp_six_gt
    obtain ⟨_, hgeom⟩ := half_log_geometry_65170000 hx
    have hgrowthL : 12 * x / (Real.log x) ^ 5 ≤
        (liFromTwo x - bgLiLower x) - (liFromTwo (x / 2) - bgLiLower (x / 2)) := by
      have hder (t : ℝ) (ht : 2 ≤ t) :
          DifferentiableAt ℝ (fun t => liFromTwo t - bgLiLower t) t :=
        (bgLiLower_gap_deriv ht).differentiableAt
      have hbound : ∀ t ∈ Set.Icc (x / 2) x,
          24 / (Real.log x) ^ 5 ≤ deriv (fun t => liFromTwo t - bgLiLower t) t := by
        intro t ht
        obtain ⟨ht2, htlog, htupper⟩ := hgeom t ht
        rw [(bgLiLower_gap_deriv ht2).deriv]
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact pow_le_pow_left₀ (by linarith) htupper 5
      have hg := gap_growth_on_half_local hhalf2 hder hbound
      convert hg using 1
      ring
    have hgrowthU : x / (2 * (Real.log x) ^ 3) ≤
        (bgLiUpper x - liFromTwo x) - (bgLiUpper (x / 2) - liFromTwo (x / 2)) := by
      have hder (t : ℝ) (ht : 2 ≤ t) :
          DifferentiableAt ℝ (fun t => bgLiUpper t - liFromTwo t) t :=
        (bgLiUpper_gap_deriv ht).differentiableAt
      have hbound : ∀ t ∈ Set.Icc (x / 2) x,
          1 / (Real.log x) ^ 3 ≤ deriv (fun t => bgLiUpper t - liFromTwo t) t := by
        intro t ht
        obtain ⟨ht2, htlog, htupper⟩ := hgeom t ht
        rw [(bgLiUpper_gap_deriv ht2).deriv]
        have hvpos : 0 < Real.log t := by linarith
        have hp : (Real.log t) ^ 3 ≤ (Real.log x) ^ 3 :=
          pow_le_pow_left₀ hvpos.le htupper 3
        have hfirst : 1 / (Real.log x) ^ 3 ≤ 1 / (Real.log t) ^ 3 :=
          div_le_div_of_nonneg_left (by norm_num) (pow_pos hvpos 3) hp
        have hsecond : 1 / (Real.log t) ^ 3 ≤ (2 * Real.log t - 12) / (Real.log t) ^ 4 := by
          apply (div_le_div_iff₀ (pow_pos hvpos 3) (pow_pos hvpos 4)).2
          have hz : 0 ≤ (Real.log t - 12) * (Real.log t) ^ 3 :=
            mul_nonneg (by linarith) (pow_nonneg hvpos.le 3)
          nlinarith [hz]
        exact hfirst.trans hsecond
      have hg := gap_growth_on_half_local hhalf2 hder hbound
      convert hg using 1
      ring
    have hupos : 0 < Real.log x := by linarith
    have hlargeL : (82 : ℝ) < 12 * x / (Real.log x) ^ 5 := by
      have hp5 : (Real.log x) ^ 5 < (22 : ℝ) ^ 5 :=
        pow_lt_pow_left₀ hu_lt hupos.le (by norm_num)
      rw [lt_div_iff₀ (pow_pos hupos 5)]
      have hnum : (82 : ℝ) * 22 ^ 5 < 12 * 65170000 := by norm_num
      nlinarith
    have hlargeU : (1458 : ℝ) < x / (2 * (Real.log x) ^ 3) := by
      have hp3 : (Real.log x) ^ 3 < (22 : ℝ) ^ 3 :=
        pow_lt_pow_left₀ hu_lt hupos.le (by norm_num)
      rw [lt_div_iff₀ (mul_pos (by norm_num) (pow_pos hupos 3))]
      have hnum : (1458 : ℝ) * (2 * 22 ^ 3) < 65170000 := by norm_num
      nlinarith
    constructor <;> linarith

theorem bg_li_normalized_of_ge_65170000 {x : ℝ} (hx : (65170000 : ℝ) ≤ x) :
    bgLiLowerNorm (Real.log x) < liFromTwo x / x ∧
      liFromTwo x / x < bgLiUpperNorm (Real.log x) := by
  have hxpos : 0 < x := by linarith
  obtain ⟨hlo, hhi⟩ := bg_li_bounds_of_ge_65170000 hx
  have hl : x * bgLiLowerNorm (Real.log x) = bgLiLower x := by
    simp only [bgLiLowerNorm, bgLiLower, div_eq_mul_inv]
    ring
  have hh : x * bgLiUpperNorm (Real.log x) = bgLiUpper x := by
    simp only [bgLiUpperNorm, bgLiUpper, div_eq_mul_inv]
    ring
  exact ⟨(lt_div_iff₀ hxpos).2 (by rw [mul_comm, hl]; exact hlo),
    (div_lt_iff₀ hxpos).2 (by rw [mul_comm, hh]; exact hhi)⟩

theorem bg_li_normalized_and_square_of_ge_65170000 {x : ℝ} (hx : (65170000 : ℝ) ≤ x) :
    let u := Real.log x
    bgLiLowerNorm u < liFromTwo x / x ∧
      liFromTwo x / x < bgLiUpperNorm u ∧
      bgLiLowerNorm (2 * u) < liFromTwo (x ^ 2) / x ^ 2 ∧
      liFromTwo (x ^ 2) / x ^ 2 < bgLiUpperNorm (2 * u) := by
  dsimp only
  have hx2 : (65170000 : ℝ) ≤ x ^ 2 := by nlinarith
  have h := bg_li_normalized_of_ge_65170000 hx
  have h2 := bg_li_normalized_of_ge_65170000 hx2
  rw [Real.log_pow] at h2
  norm_num only [Nat.cast_ofNat] at h2
  exact ⟨h.1, h.2, h2.1, h2.2⟩

/-- Uniform odd-prime count bound on `[2, X]` for all `65170000 ≤ X ≤ 4 * 10^13`. -/
theorem bmor_odd_count_uniform_bound_fc2k (bmor : BMORFiniteTheta)
    {X : ℝ} (hX : (65170000 : ℝ) ≤ X) (hcap : X ≤ (4 * 10 ^ 13 : ℝ)) :
    OddPrimeCountUniformBound X ((37 / 5 : ℝ) * (Real.sqrt X / Real.log X)) := by
  intro t ht htX
  apply le_of_lt
  have hXpos : 0 < X := by linarith
  have hlX_lo : (1799 / 100 : ℝ) < Real.log X :=
    lt_of_lt_of_le log_65170000_bounds.1 (Real.log_le_log (by norm_num) hX)
  have hlX : 0 < Real.log X := by linarith
  have hexp2_le : Real.exp 2 ≤ (65170000 : ℝ) := by
    have he1 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have he1p : 0 < Real.exp 1 := Real.exp_pos 1
    have he2 : Real.exp 2 < 9 := by
      have hadd : Real.exp ((1 : ℝ) + 1) = Real.exp 1 * Real.exp 1 := Real.exp_add 1 1
      norm_num at hadd
      rw [hadd]
      nlinarith
    linarith
  have hF0 : (4036 / 9 : ℝ) < Real.sqrt 65170000 / Real.log 65170000 := by
    have hsq : (8072 : ℝ) < Real.sqrt 65170000 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    have hlg := log_65170000_bounds
    have hlpos : 0 < Real.log (65170000 : ℝ) := by linarith
    rw [lt_div_iff₀ hlpos]
    linarith
  have hF : (4036 / 9 : ℝ) < Real.sqrt X / Real.log X :=
    lt_of_lt_of_le hF0 (sqrt_log_ratio_mono_large hexp2_le hX)
  have hcount := bmor_odd_count_theta_integral_error bmor ht (le_trans htX hcap)
  have heq : (518 / 125 : ℝ) * Real.sqrt t / Real.log t =
      (518 / 125 : ℝ) * (Real.sqrt t / Real.log t) := by ring
  rw [heq] at hcount
  have hlog2 : (2 / 3 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hconst : (2 : ℝ) / Real.log 2 < 3 := by
    apply (div_lt_iff₀ (by linarith : 0 < Real.log 2)).2
    linarith
  have h4 : Real.exp 4 < (55 : ℝ) := by
    have he : Real.exp 1 < (68 / 25 : ℝ) := by linarith [Real.exp_one_lt_d9]
    have hp : (Real.exp 1) ^ 4 < (68 / 25 : ℝ) ^ 4 :=
      pow_lt_pow_left₀ he (by positivity) (by norm_num)
    rw [Real.exp_one_pow] at hp
    norm_num at hp ⊢
    linarith
  by_cases hsmall : t ≤ Real.exp 8
  · have hf := sqrt_log_ratio_low_bound ht hsmall h4
    have hj := low_j_integral_lt_495_over_2 ht hsmall
    have herr : |oddPrimeCountReal t - liFromTwo t| < (105713 / 100 : ℝ) := by nlinarith
    have htarget : (105713 / 100 : ℝ) < (37 / 5 : ℝ) * (Real.sqrt X / Real.log X) := by linarith
    linarith
  · have hbig : Real.exp 8 ≤ t := le_of_not_ge hsmall
    have hExp : Real.exp (2 : ℝ) ≤ Real.exp 8 := Real.exp_le_exp.mpr (by norm_num)
    have hf := sqrt_log_ratio_mono_large (le_trans hExp hbig) htX
    have hg := odd_count_j_high_mono hbig (le_trans hbig htX) htX
    change Real.sqrt t / Real.log t ^ 2 ≤ Real.sqrt X / Real.log X ^ 2 at hg
    have hj := odd_count_j_global_high hbig
    have hratio : (4 : ℝ) / Real.log X ≤ 400 / 1799 := by
      apply (div_le_iff₀ hlX).2
      linarith
    have hFX : 0 ≤ Real.sqrt X / Real.log X := div_nonneg (Real.sqrt_nonneg _) hlX.le
    have hgX : Real.sqrt X / Real.log X ^ 2 = (Real.sqrt X / Real.log X) / Real.log X := by ring
    rw [hgX] at hg
    have hkg : 4 * (Real.sqrt t / Real.log t ^ 2) ≤
        (400 / 1799 : ℝ) * (Real.sqrt X / Real.log X) := by
      have hm := mul_le_mul_of_nonneg_right hratio hFX
      have heq' : (4 / Real.log X) * (Real.sqrt X / Real.log X) =
          4 * ((Real.sqrt X / Real.log X) / Real.log X) := by ring
      rw [heq'] at hm
      linarith
    have hlin : (25716 / 25 : ℝ) <
        (25716 / 25 : ℝ) * (9 / 4036) * (Real.sqrt X / Real.log X) := by linarith
    have hnum : (518 / 125 : ℝ) * (1 + 400 / 1799) +
        (25716 / 25 : ℝ) * (9 / 4036) < 37 / 5 := by norm_num
    nlinarith

private theorem odd_count_pool_mean_correlated_of_ge_65170000 {n : ℕ}
    (hn : 0 < n) (hXge : (65170000 : ℝ) ≤ (poolMaximum n : ℝ)) (D : ℝ)
    (hcount : OddPrimeCountUniformBound (poolMaximum n : ℝ) D) :
    let N : ℝ := (n * n : ℕ)
    let X : ℝ := poolMaximum n
    let u : ℝ := Real.log X
    let q : ℝ := N / X
    let E : ℝ := (((poolMaximum n - 2 : ℕ) : ℝ) * D) / (N * X)
    bgLiLowerNorm (2 * u) / q - D / N - liFromTwo 4 / (N * X) - E ≤
      ((Lucas.poolTotal n : ℝ) / N) / X ∧
    ((Lucas.poolTotal n : ℝ) / N) / X ≤
      bgLiUpperNorm (2 * u) / q + D / N - liFromTwo 4 / (N * X) + E +
        bgLiUpperNorm u / N := by
  dsimp only
  let N : ℝ := (n * n : ℕ)
  let X : ℝ := poolMaximum n
  let u : ℝ := Real.log X
  let q : ℝ := N / X
  let E : ℝ := (((poolMaximum n - 2 : ℕ) : ℝ) * D) / (N * X)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Nat.mul_pos hn hn
  have hX2 : (2 : ℝ) ≤ X := by dsimp [X]; linarith
  have hX : 0 < X := by linarith
  have hq : 0 < q := div_pos hN hX
  have hli := bg_li_normalized_and_square_of_ge_65170000 hXge
  dsimp only at hli
  have hlo := div_le_div_of_nonneg_right hli.2.2.1.le hq.le
  have hhi := div_le_div_of_nonneg_right hli.2.2.2.le hq.le
  have hquot : (liFromTwo (X ^ 2) / X ^ 2) / q = liFromTwo (X ^ 2) / (N * X) := by
    dsimp [q]; field_simp
  rw [hquot] at hlo hhi
  have hend := div_le_div_of_nonneg_right hli.2.1.le hN.le
  have hend_eq : (liFromTwo X / X) / N = liFromTwo X / (N * X) := by field_simp
  rw [hend_eq] at hend
  have hpoint0 := hcount X hX2 le_rfl
  have hpoint : |N - liFromTwo X| ≤ D := by
    dsimp [N, X] at *
    rw [oddPrimeCountReal_natCast, oddPrimePrefix_poolMaximum_card] at hpoint0
    exact hpoint0
  have hpoint_abs := abs_le.mp hpoint
  have hp1 := div_le_div_of_nonneg_right hpoint_abs.1 hN.le
  have hp2 := div_le_div_of_nonneg_right hpoint_abs.2 hN.le
  simp only [sub_div, neg_div] at hp1 hp2
  have hm := odd_count_pool_mean_continuous_bounds n hn D hcount
  dsimp only at hm
  have hidentity : 1 - (X * liFromTwo X - liFromTwo (X ^ 2) + liFromTwo 4) / (N * X) =
      liFromTwo (X ^ 2) / (N * X) + (N - liFromTwo X) / N - liFromTwo 4 / (N * X) := by
    field_simp; ring
  dsimp [N, X, u, q, E] at *
  rw [hidentity] at hm
  simp only [sub_div] at hm
  constructor <;> linarith [hm.1, hm.2, hlo, hhi, hend, hp1, hp2]

private theorem fc2k_scaled_mean_enclosure {n : ℕ} (hn : 0 < n)
    (hXge : (65170000 : ℝ) ≤ (poolMaximum n : ℝ))
    (hcount : OddPrimeCountUniformBound (poolMaximum n : ℝ)
      ((37 / 5 : ℝ) * (Real.sqrt (poolMaximum n : ℝ) / Real.log (poolMaximum n : ℝ))))
    {b : ℝ} (hub : Real.log (poolMaximum n : ℝ) ≤ b) :
    let N : ℝ := (n * n : ℕ)
    let X : ℝ := poolMaximum n
    let u : ℝ := Real.log X
    let q : ℝ := u * (N / X)
    let c : ℝ := (37 / 5 : ℝ) / 8072
    let W : ℝ := 65170000
    0 < q ∧ fwMeanA u - c ≤ q ∧ q ≤ fwMeanB u + c ∧
      (fwMeanA (2 * u) / 2 - c - c - 4 * b / W ^ 2) / q ≤
        ((Lucas.poolTotal n : ℝ) / N) / X ∧
      ((Lucas.poolTotal n : ℝ) / N) / X ≤
        (fwMeanB (2 * u) / 2 + c + c + fwMeanB u / W) / q := by
  dsimp only
  let N : ℝ := (n * n : ℕ)
  let X : ℝ := poolMaximum n
  let u : ℝ := Real.log X
  let q : ℝ := N / X
  let C : ℝ := 37 / 5
  let scale : ℝ := 8072
  let c : ℝ := C / scale
  let W : ℝ := 65170000
  let D : ℝ := C * (Real.sqrt X / u)
  let E : ℝ := (((poolMaximum n - 2 : ℕ) : ℝ) * D) / (N * X)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Nat.mul_pos hn hn
  have hX : (65170000 : ℝ) ≤ X := hXge
  have hXp : 0 < X := by linarith
  have hu : 0 < u := by
    dsimp [u]
    exact lt_trans (by norm_num)
      (lt_of_lt_of_le log_65170000_bounds.1 (Real.log_le_log (by norm_num) hX))
  have hq : 0 < q := div_pos hN hXp
  have huq : 0 < u * q := mul_pos hu hq
  have hD : 0 ≤ D := by dsimp [D, C]; positivity
  have hsqrt : Real.sqrt X ≤ X / scale := by
    dsimp [scale]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hprod : 0 ≤ X * (X - 8072 ^ 2) := mul_nonneg hXp.le (by norm_num; linarith)
    nlinarith
  have he : D * u / X ≤ c := by
    dsimp [D, c]
    apply (div_le_iff₀ hXp).2
    have h1 : C * (Real.sqrt X / u) * u = C * Real.sqrt X := by field_simp
    rw [h1]
    have hh := mul_le_mul_of_nonneg_left hsqrt (show (0 : ℝ) ≤ C by dsimp [C]; norm_num)
    have hdiv : C * (X / scale) = (C / scale) * X := by ring
    rwa [hdiv] at hh
  have hE : E ≤ D / N := by
    dsimp [E]
    have hcast : (((poolMaximum n - 2 : ℕ) : ℝ)) ≤ X := by
      dsimp [X]; exact_mod_cast Nat.sub_le (poolMaximum n) 2
    have hp := mul_le_mul_of_nonneg_right hcast hD
    apply (div_le_iff₀ (mul_pos hN hXp)).2
    have hid : D / N * (N * X) = X * D := by field_simp
    rw [hid]
    nlinarith
  have hLi0 : 0 ≤ liFromTwo 4 := by
    have hm := liFromTwo_mono (show (2 : ℝ) ≤ 2 by norm_num) (show (2 : ℝ) ≤ 4 by norm_num)
    simpa [liFromTwo] using hm
  have hLi4 : liFromTwo 4 ≤ 4 := by
    have hm := liFromTwo_le_two_mul (show (2 : ℝ) ≤ 4 by norm_num)
    linarith
  have hDN : D / N ≤ c / (u * q) := by
    have h := div_le_div_of_nonneg_right he huq.le
    have hid : (D * u / X) / (u * q) = D / N := by dsimp [q]; field_simp
    rwa [hid] at h
  have hsum : D / N + E ≤ 2 * c / (u * q) := by
    calc
      D / N + E ≤ c / (u * q) + c / (u * q) := add_le_add hDN (hE.trans hDN)
      _ = 2 * c / (u * q) := by ring
  have hsqX : W ^ 2 ≤ X ^ 2 := by dsimp [W]; nlinarith
  have hLiBound : liFromTwo 4 / (N * X) ≤ (4 * b / W ^ 2) / (u * q) := by
    have hmain : liFromTwo 4 / (N * X) ≤ 4 / (N * X) :=
      div_le_div_of_nonneg_right hLi4 (mul_pos hN hXp).le
    have hx : 4 / (N * X) ≤ 4 / (q * W ^ 2) := by
      apply (div_le_div_iff₀ (mul_pos hN hXp) (mul_pos hq (by dsimp [W]; positivity))).2
      dsimp [q]; field_simp; nlinarith
    have hid : 4 / (q * W ^ 2) = (4 * u / W ^ 2) / (u * q) := by
      dsimp [W]; field_simp
    have hfrac : (4 * u / W ^ 2) / (u * q) ≤ (4 * b / W ^ 2) / (u * q) := by
      apply div_le_div_of_nonneg_right _ huq.le
      apply div_le_div_of_nonneg_right (by linarith) (by dsimp [W]; positivity)
    exact hmain.trans ((hid ▸ hx).trans hfrac)
  have hBG : bgLiUpperNorm u / N ≤ (fwMeanB u / W) / (u * q) := by
    have hB : 0 ≤ 1 + 1 / u + 4 / u ^ 2 := by positivity
    have heq1 : bgLiUpperNorm u / N = (1 + 1 / u + 4 / u ^ 2) / (X * (u * q)) := by
      dsimp [bgLiUpperNorm, q]; field_simp
    have heq2 : (fwMeanB u / W) / (u * q) = (1 + 1 / u + 4 / u ^ 2) / (W * (u * q)) := by
      dsimp [fwMeanB]; ring
    rw [heq1, heq2]
    apply div_le_div_of_nonneg_left hB (mul_pos (by dsimp [W]; positivity) huq)
    exact mul_le_mul_of_nonneg_right hX huq.le
  have hX2 : (2 : ℝ) ≤ X := by linarith
  have hpoint := hcount X hX2 le_rfl
  have hpoint' : |N - liFromTwo X| ≤ D := by
    dsimp [N, X, D, u, C] at *
    rw [oddPrimeCountReal_natCast, oddPrimePrefix_poolMaximum_card] at hpoint
    exact hpoint
  have hp := abs_le.mp hpoint'
  have hli := bg_li_bounds_of_ge_65170000 hX
  have hcntlo : bgLiLower X - D < N := by linarith [hli.1, hp.2]
  have hcnthi : N < bgLiUpper X + D := by linarith [hli.2, hp.1]
  have hcntL : fwMeanA u - c ≤ u * q := by
    have h1 := mul_le_mul_of_nonneg_left ((div_lt_div_iff_of_pos_right hXp).2 hcntlo).le hu.le
    have hnormL : bgLiLower X / X = bgLiLowerNorm u := by
      dsimp [bgLiLower, bgLiLowerNorm, u]; field_simp
    rw [sub_div, hnormL, mul_sub, show u * (D / X) = D * u / X by ring] at h1
    rw [fwMeanA_eq_scaled (ne_of_gt hu)]
    exact (sub_le_sub_left he _).trans h1
  have hcntU : u * q ≤ fwMeanB u + c := by
    have h1 := mul_le_mul_of_nonneg_left ((div_lt_div_iff_of_pos_right hXp).2 hcnthi).le hu.le
    have hnormU : bgLiUpper X / X = bgLiUpperNorm u := by
      dsimp [bgLiUpper, bgLiUpperNorm, u]; field_simp
    rw [add_div, hnormU, mul_add, show u * (D / X) = D * u / X by ring] at h1
    rw [fwMeanB_eq_scaled (ne_of_gt hu)]
    exact h1.trans (add_le_add_right he _)
  have hm := odd_count_pool_mean_correlated_of_ge_65170000 hn hX D hcount
  dsimp only at hm
  change bgLiLowerNorm (2 * u) / q - D / N - liFromTwo 4 / (N * X) - E ≤
      ((Lucas.poolTotal n : ℝ) / N) / X ∧
    ((Lucas.poolTotal n : ℝ) / N) / X ≤
      bgLiUpperNorm (2 * u) / q + D / N - liFromTwo 4 / (N * X) + E + bgLiUpperNorm u / N at hm
  have hsqlo : bgLiLowerNorm (2 * u) / q = (fwMeanA (2 * u) / 2) / (u * q) := by
    rw [fwMeanA_eq_scaled (by linarith : (2 * u) ≠ 0)]; field_simp
  have hsqhi : bgLiUpperNorm (2 * u) / q = (fwMeanB (2 * u) / 2) / (u * q) := by
    rw [fwMeanB_eq_scaled (by linarith : (2 * u) ≠ 0)]; field_simp
  rw [hsqlo, hsqhi] at hm
  have hLi_nonneg : 0 ≤ liFromTwo 4 / (N * X) := div_nonneg hLi0 (mul_pos hN hXp).le
  have hmeanL : (fwMeanA (2 * u) / 2 - c - c - 4 * b / W ^ 2) / (u * q) ≤
      ((Lucas.poolTotal n : ℝ) / N) / X := by
    have hid : (fwMeanA (2 * u) / 2 - c - c - 4 * b / W ^ 2) / (u * q) =
        (fwMeanA (2 * u) / 2) / (u * q) - 2 * c / (u * q) - (4 * b / W ^ 2) / (u * q) := by ring
    rw [hid]
    linarith [hm.1]
  have hmeanU : ((Lucas.poolTotal n : ℝ) / N) / X ≤
      (fwMeanB (2 * u) / 2 + c + c + fwMeanB u / W) / (u * q) := by
    have hid : (fwMeanB (2 * u) / 2 + c + c + fwMeanB u / W) / (u * q) =
        (fwMeanB (2 * u) / 2) / (u * q) + 2 * c / (u * q) + (fwMeanB u / W) / (u * q) := by ring
    rw [hid]
    linarith [hm.2]
  exact ⟨huq, hcntL, hcntU, hmeanL, hmeanU⟩

private theorem fc2k_mean_cells_low (i : ℕ) (hi : i < 41) :
    let a : ℝ := (287 + (i : ℝ)) / 16
    let b : ℝ := (288 + (i : ℝ)) / 16
    let c : ℝ := (37 / 5 : ℝ) / 8072
    let W : ℝ := 65170000
    0 < fwMeanA b - c ∧
      (959 / 2000 : ℝ) < (fwMeanA (2 * b) / 2 - 2 * c - 4 * b / W ^ 2) / (fwMeanB a + c) ∧
      (fwMeanB (2 * a) / 2 + 2 * c + fwMeanB a / W) / (fwMeanA b - c) < (491 / 1000 : ℝ) := by
  have hbound : i ≤ 40 := by omega
  interval_cases i <;> norm_num [fwMeanA, fwMeanB]

private theorem fc2k_mean_cells_high (k : ℕ) (hk : k < 40) :
    let a : ℝ := (328 + (k : ℝ)) / 16
    let b : ℝ := (329 + (k : ℝ)) / 16
    let c : ℝ := (37 / 5 : ℝ) / 8072
    let W : ℝ := 65170000
    0 < fwMeanA b - c ∧
      (959 / 2000 : ℝ) < (fwMeanA (2 * b) / 2 - 2 * c - 4 * b / W ^ 2) / (fwMeanB a + c) ∧
      (fwMeanB (2 * a) / 2 + 2 * c + fwMeanB a / W) / (fwMeanA b - c) < (491 / 1000 : ℝ) := by
  have hbound : k ≤ 39 := by omega
  interval_cases k <;> norm_num [fwMeanA, fwMeanB]

private theorem fc2k_mean_cells_all (i : ℕ) (hi : i < 81) :
    let a : ℝ := (287 + (i : ℝ)) / 16
    let b : ℝ := (288 + (i : ℝ)) / 16
    let c : ℝ := (37 / 5 : ℝ) / 8072
    let W : ℝ := 65170000
    0 < fwMeanA b - c ∧
      (959 / 2000 : ℝ) < (fwMeanA (2 * b) / 2 - 2 * c - 4 * b / W ^ 2) / (fwMeanB a + c) ∧
      (fwMeanB (2 * a) / 2 + 2 * c + fwMeanB a / W) / (fwMeanA b - c) < (491 / 1000 : ℝ) := by
  by_cases h41 : i < 41
  · exact fc2k_mean_cells_low i h41
  · have hk : i - 41 < 40 := by omega
    have h := fc2k_mean_cells_high (i - 41) hk
    have hi_eq : (i : ℝ) = 41 + ((i - 41 : ℕ) : ℝ) := by
      have hn : i = 41 + (i - 41) := by omega
      conv_lhs => rw [hn]
      push_cast
      rfl
    have ha : (287 + (i : ℝ)) / 16 = (328 + ((i - 41 : ℕ) : ℝ)) / 16 := by rw [hi_eq]; ring
    have hb : (288 + (i : ℝ)) / 16 = (329 + ((i - 41 : ℕ) : ℝ)) / 16 := by rw [hi_eq]; ring
    dsimp only at h ⊢
    rwa [ha, hb]

/-- Upper bound on `poolMaximum n` and its logarithm throughout `[2001, 19483]`. -/
theorem fc2k_poolMaximum_upper_and_log_lt_23
    (upper : RSIndexUpper) {n : ℕ} (hnlo : 2001 ≤ n) (hnhi : n ≤ 19483) :
    poolMaximum n < 9120000000 ∧ Real.log (poolMaximum n : ℝ) < 23 := by
  have hj6 : 6 ≤ n * n + 1 := (tail_prime_index_domains hnlo).1
  have hjnat : n * n + 1 ≤ 379587290 := by
    have hm : n * n ≤ 19483 * 19483 := Nat.mul_le_mul hnhi hnhi
    omega
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hjpos : 0 < j := by dsimp [j]; positivity
  have hjgt : 1 < j := by dsimp [j]; exact_mod_cast (show 1 < n * n + 1 by omega)
  have hjreal : j ≤ 379587290 := by dsimp [j]; exact_mod_cast hjnat
  have hjlt : j < (2 : ℝ) ^ 29 := by norm_num at hjreal ⊢; linarith
  have hlog2 := Real.log_two_lt_d9
  have hlogj : Real.log j < 205 / 10 := by
    have h := Real.log_lt_log hjpos hjlt
    rw [Real.log_pow] at h
    norm_num at h
    linarith
  have hlogjpos : 0 < Real.log j := Real.log_pos hjgt
  have hloglogj : Real.log (Real.log j) < 35 / 10 := by
    have h1 := Real.log_lt_log hlogjpos hlogj
    have h2 := Real.log_lt_log (by norm_num : (0 : ℝ) < 205 / 10)
      (by norm_num : (205 / 10 : ℝ) < 2 ^ 5)
    rw [Real.log_pow] at h2
    norm_num at h2
    linarith
  have hu := poolMaximum_upper upper n hj6
  have hXreal : (poolMaximum n : ℝ) < 9120000000 := by
    have hsum : Real.log j + Real.log (Real.log j) < 24 := by linarith
    have hprod := mul_lt_mul_of_pos_left hsum hjpos
    calc
      (poolMaximum n : ℝ) < j * 24 := lt_trans hu hprod
      _ ≤ 379587290 * 24 := mul_le_mul_of_nonneg_right hjreal (by norm_num)
      _ < 9120000000 := by norm_num
  refine ⟨by exact_mod_cast hXreal, ?_⟩
  have hXp : (0 : ℝ) < (poolMaximum n : ℝ) := by exact_mod_cast (poolMaximum_prime n).pos
  have hpow : (poolMaximum n : ℝ) ^ 10 < (2 : ℝ) ^ 331 := by
    have h1 : (poolMaximum n : ℝ) ^ 10 < (9120000000 : ℝ) ^ 10 :=
      pow_lt_pow_left₀ hXreal hXp.le (by norm_num)
    have h2 : (9120000000 : ℝ) ^ 10 < (2 : ℝ) ^ 331 := by
      exact_mod_cast (by decide +kernel : (9120000000 : ℕ) ^ 10 < 2 ^ 331)
    exact h1.trans h2
  have hlg := Real.log_lt_log (pow_pos hXp 10) hpow
  rw [Real.log_pow, Real.log_pow] at hlg
  push_cast at hlg
  linarith

/-- Normalized prescribed-pool mean bounds throughout `2001 ≤ n ≤ 19483`:
    `959 / 2000 < m / X` (`0.4795 < m / X`) and `m / X < 491 / 1000` (`m / X < 0.4910`). -/
theorem fc2k_pool_normalized_mean_bounds
    (bmor : BMORFiniteTheta) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 2001 ≤ n) (hnhi : n ≤ 19483) :
    (959 / 2000 : ℝ) < ((Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ)) / (poolMaximum n : ℝ) ∧
    ((Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ)) / (poolMaximum n : ℝ) < (491 / 1000 : ℝ) := by
  obtain ⟨hXlo_nat, _⟩ := poolMaximum_gt_65170000_and_log_gt sharp hnlo
  obtain ⟨hXhi_nat, hloghi⟩ := fc2k_poolMaximum_upper_and_log_lt_23 upper hnlo hnhi
  have hXge : (65170000 : ℝ) ≤ (poolMaximum n : ℝ) :=
    le_of_lt (Nat.cast_lt.mpr hXlo_nat)
  have hXcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ) := by
    have h1 : (poolMaximum n : ℝ) < 9120000000 := Nat.cast_lt.mpr hXhi_nat
    linarith
  let u : ℝ := Real.log (poolMaximum n : ℝ)
  have hloglo : (287 / 16 : ℝ) ≤ u := by
    have h1 : (1799 / 100 : ℝ) < u :=
      lt_of_lt_of_le log_65170000_bounds.1 (Real.log_le_log (by norm_num) hXge)
    linarith
  let z : ℝ := 16 * u - 287
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hzupper : z < 81 := by dsimp [z, u]; linarith
  let i : ℕ := ⌊z⌋₊
  have hil : (i : ℝ) ≤ z := Nat.floor_le hz
  have hiu : z < (i : ℝ) + 1 := Nat.lt_floor_add_one z
  have hi : i < 81 := by exact_mod_cast (lt_of_le_of_lt hil hzupper)
  let a : ℝ := (287 + (i : ℝ)) / 16
  let b : ℝ := (288 + (i : ℝ)) / 16
  let c : ℝ := (37 / 5 : ℝ) / 8072
  let W : ℝ := 65170000
  let q : ℝ := u * (((n * n : ℕ) : ℝ) / (poolMaximum n : ℝ))
  let m : ℝ := ((Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ)) / (poolMaximum n : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hau : a ≤ u := by dsimp [a, z] at *; linarith
  have hub : u ≤ b := by dsimp [b, z] at *; linarith
  have hW : 0 < W := by dsimp [W]; positivity
  have hcert := fc2k_mean_cells_all i hi
  dsimp only at hcert
  change 0 < fwMeanA b - c ∧
    (959 / 2000 : ℝ) < (fwMeanA (2 * b) / 2 - 2 * c - 4 * b / W ^ 2) / (fwMeanB a + c) ∧
    (fwMeanB (2 * a) / 2 + 2 * c + fwMeanB a / W) / (fwMeanA b - c) < (491 / 1000 : ℝ) at hcert
  have hden : 0 < fwMeanB a + c := by
    have hB : 0 < fwMeanB a := by dsimp [fwMeanB]; positivity
    have hc : 0 < c := by dsimp [c]; norm_num
    linarith
  have hnumlo : 0 ≤ fwMeanA (2 * b) / 2 - 2 * c - 4 * b / W ^ 2 := by
    have ht := (lt_div_iff₀ hden).mp hcert.2.1
    have hp := mul_pos (by norm_num : (0 : ℝ) < 959 / 2000) hden
    linarith
  have hnumhi : 0 ≤ fwMeanB (2 * a) / 2 + 2 * c + fwMeanB a / W := by
    have ha2 : 0 < 2 * a := by positivity
    have hb2 : 0 < fwMeanB (2 * a) := by dsimp [fwMeanB]; positivity
    have hb1 : 0 < fwMeanB a := by dsimp [fwMeanB]; positivity
    have hc : 0 < c := by dsimp [c]; norm_num
    positivity
  have hcount := bmor_odd_count_uniform_bound_fc2k bmor hXge hXcap
  have hs := fc2k_scaled_mean_enclosure (by omega : 0 < n) hXge hcount hub
  dsimp only at hs
  change 0 < q ∧ fwMeanA u - c ≤ q ∧ q ≤ fwMeanB u + c ∧
    (fwMeanA (2 * u) / 2 - c - c - 4 * b / W ^ 2) / q ≤ m ∧
    m ≤ (fwMeanB (2 * u) / 2 + c + c + fwMeanB u / W) / q at hs
  have ht := fw_mean_cell_transport ha hau hub hW hs.1 hs.2.1 hs.2.2.1
    (le_refl c) (le_refl c) (le_refl (4 * b / W ^ 2)) (le_refl (fwMeanB u / W))
    hcert.1 hnumlo hnumhi hs.2.2.2.1 hs.2.2.2.2
  change (959 / 2000 : ℝ) < m ∧ m < (491 / 1000 : ℝ)
  constructor <;> linarith [hcert.2.1, hcert.2.2, ht.1, ht.2]

/-- Unnormalized prescribed-pool mean bounds throughout `2001 ≤ n ≤ 19483`. -/
theorem fc2k_pool_mean_bounds
    (bmor : BMORFiniteTheta) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 2001 ≤ n) (hnhi : n ≤ 19483) :
    (959 / 2000 : ℝ) * (poolMaximum n : ℝ) <
      (Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ) ∧
    (Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ) <
      (491 / 1000 : ℝ) * (poolMaximum n : ℝ) := by
  have hX : 0 < (poolMaximum n : ℝ) := by exact_mod_cast (poolMaximum_prime n).pos
  obtain ⟨hlo, hhi⟩ := fc2k_pool_normalized_mean_bounds bmor sharp upper hnlo hnhi
  exact ⟨(lt_div_iff₀ hX).mp hlo, (div_lt_iff₀ hX).mp hhi⟩

end

end Sude
