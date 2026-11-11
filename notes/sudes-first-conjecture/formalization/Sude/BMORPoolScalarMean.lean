import Sude.BMORPoolContinuousMean
import Sude.LiBGUnconditional

/-! Conditional scalar enclosure for the normalized pool mean, retaining the
exact `Li(4)` lower endpoint and one `Li(X)` discretization allowance. -/
namespace Sude
noncomputable section

/-- If Li is bounded at the actual pool maximum and its square, those bounds
transport to the normalized mean without discarding endpoint contributions. -/
theorem bmor_pool_mean_scalar_of_li_bounds (h : BMORFinitePiFour) (n : ℕ)
    (hn : 0 < n)
    (hlog : 22 ≤ Real.log (poolMaximum n : ℝ))
    (hcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ))
    (LX UX LS US : ℝ)
    (hLX : LX ≤ liFromTwo (poolMaximum n : ℝ))
    (hUX : liFromTwo (poolMaximum n : ℝ) ≤ UX)
    (hLS : LS ≤ liFromTwo ((poolMaximum n : ℝ)^2))
    (hUS : liFromTwo ((poolMaximum n : ℝ)^2) ≤ US) :
    let N : ℝ := (n * n : ℕ)
    let X : ℝ := poolMaximum n
    let D : ℝ := (281649 / 62500 : ℝ) * (Real.sqrt X / Real.log X)
    let E : ℝ := (((poolMaximum n - 2 : ℕ) : ℝ) * D) / (N * X)
    let lowA : ℝ := X * LX - US + liFromTwo 4
    let highA : ℝ := X * UX - LS + liFromTwo 4
    1 - highA / (N * X) - E ≤ ((Lucas.poolTotal n : ℝ) / N) / X ∧
      ((Lucas.poolTotal n : ℝ) / N) / X ≤
        1 - lowA / (N * X) + E + UX / (N * X) := by
  dsimp only
  let N : ℝ := (n * n : ℕ)
  let X : ℝ := poolMaximum n
  let A : ℝ := X * liFromTwo X - liFromTwo (X ^ 2) + liFromTwo 4
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Nat.mul_pos hn hn
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hNX : 0 < N * X := mul_pos hN hX
  have hAlo : X * LX - US + liFromTwo 4 ≤ A := by
    dsimp [A]; nlinarith [mul_le_mul_of_nonneg_left hLX hX.le]
  have hAhi : A ≤ X * UX - LS + liFromTwo 4 := by
    dsimp [A]; nlinarith [mul_le_mul_of_nonneg_left hUX hX.le]
  have ha := div_le_div_of_nonneg_right hAlo hNX.le
  have hb := div_le_div_of_nonneg_right hAhi hNX.le
  have hc := div_le_div_of_nonneg_right hUX hNX.le
  have hcont := bmor_pool_mean_continuous_bounds h n hn hlog hcap
  dsimp only at hcont
  constructor <;> dsimp [N, X, A] at * <;> linarith

/-- Using the unconditional BG estimates gives an explicit comparison, while
keeping the genuine pool-size, BMOR error and Li(4) terms. -/
theorem bmor_pool_mean_bg_scalar_bounds (h : BMORFinitePiFour) (n : ℕ)
    (hn : 0 < n)
    (hlog : 22 ≤ Real.log (poolMaximum n : ℝ))
    (hcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ)) :
    let N : ℝ := (n * n : ℕ)
    let X : ℝ := poolMaximum n
    let D : ℝ := (281649 / 62500 : ℝ) * (Real.sqrt X / Real.log X)
    let E : ℝ := (((poolMaximum n - 2 : ℕ) : ℝ) * D) / (N * X)
    let lowA : ℝ := X * bgLiLower X - bgLiUpper (X ^ 2) + liFromTwo 4
    let highA : ℝ := X * bgLiUpper X - bgLiLower (X ^ 2) + liFromTwo 4
    1 - highA / (N * X) - E ≤ ((Lucas.poolTotal n : ℝ) / N) / X ∧
      ((Lucas.poolTotal n : ℝ) / N) / X ≤
        1 - lowA / (N * X) + E + bgLiUpper X / (N * X) := by
  have hX : (2 : ℝ) ≤ (poolMaximum n : ℝ) := by
    exact_mod_cast (poolMaximum_prime n).two_le
  have hsqX : (2 : ℝ) ≤ (poolMaximum n : ℝ)^2 := by nlinarith
  have hlog2 : (22 : ℝ) ≤ Real.log ((poolMaximum n : ℝ)^2) := by
    rw [Real.log_pow]; norm_num; linarith
  have hbX := bg_li_bounds_of_log_ge_22 hX hlog
  have hbS := bg_li_bounds_of_log_ge_22 hsqX hlog2
  exact bmor_pool_mean_scalar_of_li_bounds h n hn hlog hcap
    (bgLiLower (poolMaximum n : ℝ)) (bgLiUpper (poolMaximum n : ℝ))
    (bgLiLower ((poolMaximum n : ℝ)^2)) (bgLiUpper ((poolMaximum n : ℝ)^2))
    hbX.1.le hbX.2.le hbS.1.le hbS.2.le

/-- At the actual pool maximum, BMOR bounds the difference between the exact
`n²` odd-prime count and the integral normalized at 2. -/
theorem bmor_poolMaximum_count_error (h : BMORFinitePiFour) (n : ℕ)
    (hcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ)) :
    |((n * n : ℕ) : ℝ) - liFromTwo (poolMaximum n : ℝ)| ≤
      (281649 / 62500 : ℝ) *
        (Real.sqrt (poolMaximum n : ℝ) / Real.log (poolMaximum n : ℝ)) := by
  have hx : (2 : ℝ) ≤ (poolMaximum n : ℝ) := by
    exact_mod_cast (poolMaximum_prime n).two_le
  have hcount := bmor_odd_count_four_pointwise h hx hcap
  rw [oddPrimeCountReal_natCast, oddPrimePrefix_poolMaximum_card] at hcount
  exact hcount

/-- BG's inequalities give explicit lower and upper bounds for the exact
pool count, with BMOR's endpoint error retained in full. -/
theorem bmor_poolMaximum_count_bg_bounds (h : BMORFinitePiFour) (n : ℕ)
    (hlog : 22 ≤ Real.log (poolMaximum n : ℝ))
    (hcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ)) :
    let X : ℝ := poolMaximum n
    let D : ℝ := (281649 / 62500 : ℝ) * (Real.sqrt X / Real.log X)
    bgLiLower X - D < ((n * n : ℕ) : ℝ) ∧
      ((n * n : ℕ) : ℝ) < bgLiUpper X + D := by
  dsimp only
  have hx : (2 : ℝ) ≤ (poolMaximum n : ℝ) := by
    exact_mod_cast (poolMaximum_prime n).two_le
  have hb := bg_li_bounds_of_log_ge_22 hx hlog
  have he := bmor_poolMaximum_count_error h n hcap
  rcases abs_le.mp he with ⟨he₁, he₂⟩
  constructor <;> linarith [hb.1, hb.2]

/-- Normalized form: divide the same two bounds by the positive pool maximum. -/
theorem bmor_poolMaximum_count_bg_bounds_normalized (h : BMORFinitePiFour) (n : ℕ)
    (hlog : 22 ≤ Real.log (poolMaximum n : ℝ))
    (hcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ)) :
    let X : ℝ := poolMaximum n
    let D : ℝ := (281649 / 62500 : ℝ) * (Real.sqrt X / Real.log X)
    (bgLiLower X - D) / X < ((n * n : ℕ) : ℝ) / X ∧
      ((n * n : ℕ) : ℝ) / X < (bgLiUpper X + D) / X := by
  dsimp only
  have hx : 0 < (poolMaximum n : ℝ) := by
    have htwo := (poolMaximum_prime n).two_le
    exact_mod_cast (by omega : 0 < poolMaximum n)
  have h := bmor_poolMaximum_count_bg_bounds h n hlog hcap
  dsimp only at h
  exact ⟨div_lt_div_of_pos_right h.1 hx, div_lt_div_of_pos_right h.2 hx⟩


/-- Normalized BG lower expression at logarithm u. -/
def bgLiLowerNorm (u : ℝ) : ℝ :=
  1 / u + 1 / u^2 + 2 / u^3 + 6 / u^4

/-- Normalized BG upper expression at logarithm u. -/
def bgLiUpperNorm (u : ℝ) : ℝ :=
  1 / u + 1 / u^2 + 4 / u^3

/-- Unconditional BG comparisons for the normalized Li value. -/
theorem bg_li_normalized_of_log_ge_22 {x : ℝ} (hx : 2 ≤ x)
    (hu : 22 ≤ Real.log x) :
    bgLiLowerNorm (Real.log x) < liFromTwo x / x ∧
      liFromTwo x / x < bgLiUpperNorm (Real.log x) := by
  have hxpos : 0 < x := by linarith
  obtain ⟨hlo, hhi⟩ := bg_li_bounds_of_log_ge_22 hx hu
  have hl : x * bgLiLowerNorm (Real.log x) = bgLiLower x := by
    simp only [bgLiLowerNorm, bgLiLower, div_eq_mul_inv]
    ring
  have hh : x * bgLiUpperNorm (Real.log x) = bgLiUpper x := by
    simp only [bgLiUpperNorm, bgLiUpper, div_eq_mul_inv]
    ring
  constructor
  · apply (lt_div_iff₀ hxpos).2
    rw [mul_comm, hl]
    exact hlo
  · apply (div_lt_iff₀ hxpos).2
    rw [mul_comm, hh]
    exact hhi

/-- Both x and x² are controlled using u = log x, with exact factor 2. -/
theorem bg_li_normalized_and_square {x : ℝ} (hx : 2 ≤ x)
    (hu : 22 ≤ Real.log x) :
    let u := Real.log x
    bgLiLowerNorm u < liFromTwo x / x ∧
      liFromTwo x / x < bgLiUpperNorm u ∧
      bgLiLowerNorm (2 * u) < liFromTwo (x^2) / x^2 ∧
      liFromTwo (x^2) / x^2 < bgLiUpperNorm (2 * u) := by
  dsimp only
  have hx2 : 2 ≤ x^2 := by nlinarith
  have hu2 : 22 ≤ Real.log (x^2) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  have h := bg_li_normalized_of_log_ge_22 hx hu
  have h2 := bg_li_normalized_of_log_ge_22 hx2 hu2
  rw [Real.log_pow] at h2
  norm_num only [Nat.cast_ofNat] at h2
  exact ⟨h.1,h.2,h2.1,h2.2⟩

/-- Exact dimensionless Li-integral bounds, before numerical evaluation of u. -/
theorem bg_li_integral_normalized {x : ℝ} (hx : 2 ≤ x)
    (hu : 22 ≤ Real.log x) :
    let u := Real.log x
    bgLiLowerNorm u - bgLiUpperNorm (2*u) + liFromTwo 4 / x^2 <
      (∫ t in (2 : ℝ)..x, liFromTwo t) / x^2 ∧
    (∫ t in (2 : ℝ)..x, liFromTwo t) / x^2 <
      bgLiUpperNorm u - bgLiLowerNorm (2*u) + liFromTwo 4 / x^2 := by
  dsimp only
  obtain ⟨hl,hu',hl2,hu2⟩ := bg_li_normalized_and_square hx hu
  have hxne : x ≠ 0 := by linarith
  have hid : (x * liFromTwo x - liFromTwo (x^2) + liFromTwo 4) / x^2 =
      liFromTwo x / x - liFromTwo (x^2) / x^2 + liFromTwo 4 / x^2 := by
    field_simp
  rw [liFromTwo_integral_identity hx, hid]
  constructor <;> linarith

/-- Simplified normalized lower integral expression. -/
def bgLiIntegralLowerNorm (u : ℝ) : ℝ :=
  1/(2*u) + 3/(4*u^2) + 3/(2*u^3) + 6/u^4

/-- Simplified normalized upper integral expression. -/
def bgLiIntegralUpperNorm (u : ℝ) : ℝ :=
  1/(2*u) + 3/(4*u^2) + 15/(4*u^3) - 3/(8*u^4)

theorem bg_li_integral_norm_simplify {u : ℝ} (hu : u ≠ 0) :
    bgLiLowerNorm u - bgLiUpperNorm (2*u) = bgLiIntegralLowerNorm u ∧
      bgLiUpperNorm u - bgLiLowerNorm (2*u) = bgLiIntegralUpperNorm u := by
  constructor <;>
    simp only [bgLiLowerNorm, bgLiUpperNorm, bgLiIntegralLowerNorm, bgLiIntegralUpperNorm] <;>
    field_simp <;> ring

/-- Exact dimensionless Li-integral bounds in the simplified BG forms. -/
theorem bg_li_integral_simplified_normalized {x : ℝ} (hx : 2 ≤ x)
    (hu : 22 ≤ Real.log x) :
    let u := Real.log x
    bgLiIntegralLowerNorm u + liFromTwo 4 / x^2 <
      (∫ t in (2 : ℝ)..x, liFromTwo t) / x^2 ∧
    (∫ t in (2 : ℝ)..x, liFromTwo t) / x^2 <
      bgLiIntegralUpperNorm u + liFromTwo 4 / x^2 := by
  dsimp only
  have h := bg_li_integral_normalized hx hu
  dsimp only at h
  have hu0 : Real.log x ≠ 0 := by linarith
  have hs := bg_li_integral_norm_simplify hu0
  rw [hs.1, hs.2] at h
  exact h



/-- Explicit scalar enclosure for the actual normalized mean and pool count,
with `u = log X` and `q = N / X`. BMOR is applied only at `X`; the Li
bounds at `X²` are elementary. No numerical mean interval is asserted. -/
theorem bmor_pool_mean_dimensionless_bounds (h : BMORFinitePiFour) (n : ℕ)
    (hn : 0 < n) (hlog : 22 ≤ Real.log (poolMaximum n : ℝ))
    (hcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ)) :
    let N : ℝ := (n * n : ℕ)
    let X : ℝ := poolMaximum n
    let u : ℝ := Real.log X
    let q : ℝ := N / X
    let D : ℝ := (281649 / 62500 : ℝ) * (Real.sqrt X / u)
    let E : ℝ := (((poolMaximum n - 2 : ℕ) : ℝ) * D) / (N * X)
    bgLiLowerNorm u - D / X < q ∧ q < bgLiUpperNorm u + D / X ∧
    (1 - (bgLiIntegralUpperNorm u + liFromTwo 4 / X^2) / q - E ≤
      ((Lucas.poolTotal n : ℝ) / N) / X) ∧
    (((Lucas.poolTotal n : ℝ) / N) / X ≤
      1 - (bgLiIntegralLowerNorm u + liFromTwo 4 / X^2) / q + E +
        bgLiUpperNorm u / N) := by
  dsimp only
  let N : ℝ := (n * n : ℕ)
  let X : ℝ := poolMaximum n
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Nat.mul_pos hn hn
  have hX2 : (2 : ℝ) ≤ X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).two_le
  have hX : 0 < X := by linarith
  have hq : 0 < N / X := div_pos hN hX
  have hli := bg_li_normalized_of_log_ge_22 hX2 hlog
  have hpoint := bmor_poolMaximum_count_error h n hcap
  have hpoint' := abs_le.mp hpoint
  have hpointlo := div_le_div_of_nonneg_right hpoint'.1 hX.le
  have hpointhi := div_le_div_of_nonneg_right hpoint'.2 hX.le
  simp only [sub_div, neg_div] at hpointlo hpointhi
  have hcount : bgLiLowerNorm (Real.log X) -
      (281649 / 62500 : ℝ) * (Real.sqrt X / Real.log X) / X < N / X ∧
      N / X < bgLiUpperNorm (Real.log X) +
        (281649 / 62500 : ℝ) * (Real.sqrt X / Real.log X) / X := by
    dsimp [N, X] at *
    constructor <;> linarith [hli.1, hli.2, hpointlo, hpointhi]
  have hi := bg_li_integral_simplified_normalized hX2 hlog
  dsimp only at hi
  rw [liFromTwo_integral_identity hX2] at hi
  have hlo := div_le_div_of_nonneg_right hi.1.le hq.le
  have hhi := div_le_div_of_nonneg_right hi.2.le hq.le
  have hquot : ((X * liFromTwo X - liFromTwo (X^2) + liFromTwo 4) / X^2) /
      (N / X) = (X * liFromTwo X - liFromTwo (X^2) + liFromTwo 4) / (N * X) := by
    field_simp
  rw [hquot] at hlo hhi
  have hend := div_le_div_of_nonneg_right hli.2.le hN.le
  have hend_eq : (liFromTwo X / X) / N = liFromTwo X / (N * X) := by
    field_simp
  rw [hend_eq] at hend
  have hm := bmor_pool_mean_continuous_bounds h n hn hlog hcap
  dsimp only at hm
  constructor
  · simpa [N, X] using hcount.1
  constructor
  · simpa [N, X] using hcount.2
  constructor <;> dsimp [N, X] at * <;> linarith


end
end Sude
