import Sude.OddCountCoarseErrors
import Sude.OddCountCorrelatedMean
import Sude.FWMeanFunctions

/-! Scaled pool-count and correlated mean bounds from an explicitly supplied
aggregate count estimate, suitable for transport to a logarithm cell. -/
namespace Sude
noncomputable section

/-- The correlated bounds for the actual pool, scaled by `u = log X`.
The error and endpoint charges are bounded separately by the explicit
finite-range constants; no target mean interval is assumed. -/
theorem odd_count_mean_scaled_bounds
    {n : ℕ} (hn : 0 < n)
    (hlog : 22 ≤ Real.log (poolMaximum n : ℝ))
    (hXbound : (2 : ℝ)^32 ≤ (poolMaximum n : ℝ))
    (C scale : ℝ) (hC : 0 ≤ C)
    (hsqrt : Real.sqrt (poolMaximum n : ℝ) ≤ (poolMaximum n : ℝ) / scale)
    (hcount : OddPrimeCountUniformBound (poolMaximum n : ℝ)
      (C * (Real.sqrt (poolMaximum n : ℝ) / Real.log (poolMaximum n : ℝ))))
    {b : ℝ} (hub : Real.log (poolMaximum n : ℝ) ≤ b) :
    let N : ℝ := (n * n : ℕ)
    let X : ℝ := poolMaximum n
    let u : ℝ := Real.log X
    let q : ℝ := u * (N / X)
    let c : ℝ := C / scale
    let W : ℝ := 2 ^ 32
    0 < q ∧ fwMeanA u - c ≤ q ∧ q ≤ fwMeanB u + c ∧
      (fwMeanA (2*u)/2 - c - c - 4*b/W^2)/q ≤
        ((Lucas.poolTotal n : ℝ) / N) / X ∧
      ((Lucas.poolTotal n : ℝ) / N) / X ≤
        (fwMeanB (2*u)/2 + c + c + fwMeanB u/W)/q := by
  dsimp only
  let N : ℝ := (n * n : ℕ)
  let X : ℝ := poolMaximum n
  let u : ℝ := Real.log X
  let q : ℝ := N / X
  let c : ℝ := C / scale
  let W : ℝ := 2 ^ 32
  let D : ℝ := C * (Real.sqrt X / u)
  let E : ℝ := (((poolMaximum n - 2 : ℕ) : ℝ) * D) / (N * X)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n)
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hu : 0 < u := by dsimp [u]; linarith
  have hq : 0 < q := div_pos hN hX
  have huq : 0 < u*q := mul_pos hu hq
  have hW : 0 < W := by dsimp [W]; positivity
  have hce := odd_count_mean_coarse_errors hn hlog hXbound C scale hC hsqrt
  dsimp only at hce
  change D*u/X ≤ c ∧ E ≤ D/N ∧
    (0 ≤ liFromTwo 4 ∧ liFromTwo 4 ≤ 4) ∧
    D/N + E ≤ 2*c/(u*q) ∧
    liFromTwo 4/(N*X) ≤ 4*u/(W^2*(u*q)) ∧
    bgLiUpperNorm u/N ≤ fwMeanB u/(W*(u*q)) at hce
  have hX2 : (2 : ℝ) ≤ X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).two_le
  have hpoint := hcount X hX2 le_rfl
  have hpoint' : |N - liFromTwo X| ≤ D := by
    dsimp [N, X, D, u] at *
    rw [oddPrimeCountReal_natCast, oddPrimePrefix_poolMaximum_card] at hpoint
    exact hpoint
  have hp := abs_le.mp hpoint'
  have hli := bg_li_bounds_of_log_ge_22 hX2 hlog
  have hcntlo : bgLiLower X - D < N := by linarith [hli.1, hp.2]
  have hcnthi : N < bgLiUpper X + D := by linarith [hli.2, hp.1]
  have hcnt : (bgLiLower X - D)/X < q ∧ q < (bgLiUpper X + D)/X := by
    dsimp [q]
    exact ⟨(div_lt_div_iff_of_pos_right hX).2 hcntlo,
      (div_lt_div_iff_of_pos_right hX).2 hcnthi⟩
  have hA : fwMeanA u = u * bgLiLowerNorm u := fwMeanA_eq_scaled (ne_of_gt hu)
  have hB : fwMeanB u = u * bgLiUpperNorm u := fwMeanB_eq_scaled (ne_of_gt hu)
  have hcntlo := mul_le_mul_of_nonneg_left hcnt.1.le hu.le
  have hcnthi := mul_le_mul_of_nonneg_left hcnt.2.le hu.le
  change u * ((bgLiLower X - D)/X) ≤ u*q at hcntlo
  change u*q ≤ u * ((bgLiUpper X + D)/X) at hcnthi
  have hnormL : bgLiLower X / X = bgLiLowerNorm u := by
    dsimp [bgLiLower, bgLiLowerNorm, u]
    field_simp
  have hnormU : bgLiUpper X / X = bgLiUpperNorm u := by
    dsimp [bgLiUpper, bgLiUpperNorm, u]
    field_simp
  rw [sub_div, hnormL] at hcntlo
  rw [add_div, hnormU] at hcnthi
  have hscale : u * (D / X) = D * u / X := by ring
  rw [mul_sub, hscale] at hcntlo
  rw [mul_add, hscale] at hcnthi
  have hcntL : fwMeanA u - c ≤ u*q := by
    rw [hA]
    exact (sub_le_sub_left hce.1 _).trans hcntlo
  have hcntU : u*q ≤ fwMeanB u + c := by
    rw [hB]
    exact hcnthi.trans (add_le_add_right hce.1 _)
  have hm := odd_count_pool_mean_correlated_bounds n hn hlog D hcount
  dsimp only at hm
  change bgLiLowerNorm (2*u)/q - D/N - liFromTwo 4/(N*X) - E ≤
      ((Lucas.poolTotal n : ℝ)/N)/X ∧
    ((Lucas.poolTotal n : ℝ)/N)/X ≤
      bgLiUpperNorm (2*u)/q + D/N - liFromTwo 4/(N*X) + E + bgLiUpperNorm u/N at hm
  have hsqlo : bgLiLowerNorm (2*u)/q = (fwMeanA (2*u)/2)/(u*q) := by
    rw [fwMeanA_eq_scaled (by linarith : (2*u) ≠ 0)]
    field_simp
  have hsqhi : bgLiUpperNorm (2*u)/q = (fwMeanB (2*u)/2)/(u*q) := by
    rw [fwMeanB_eq_scaled (by linarith : (2*u) ≠ 0)]
    field_simp
  rw [hsqlo, hsqhi] at hm
  have hLi4 : 0 ≤ liFromTwo 4 / (N*X) := div_nonneg hce.2.2.1.1 (mul_pos hN hX).le
  have hLiBound : liFromTwo 4/(N*X) ≤ (4*b/W^2)/(u*q) := by
    have hc := hce.2.2.2.2.1
    have hfrac : 4*u/(W^2*(u*q)) ≤ 4*b/(W^2*(u*q)) :=
      div_le_div_of_nonneg_right (by nlinarith [hub]) (by positivity)
    have hid : 4*b/(W^2*(u*q)) = (4*b/W^2)/(u*q) := by ring
    linarith
  have hEB : fwMeanB u/(W*(u*q)) = (fwMeanB u/W)/(u*q) := by ring
  have hmeanL : (fwMeanA (2*u)/2 - c - c - 4*b/W^2)/(u*q) ≤
      ((Lucas.poolTotal n : ℝ)/N)/X := by
    have he := hce.2.2.2.1
    have hid : (fwMeanA (2*u)/2 - c - c - 4*b/W^2)/(u*q) =
      (fwMeanA (2*u)/2)/(u*q) - 2*c/(u*q) - (4*b/W^2)/(u*q) := by ring
    rw [hid]
    linarith [hm.1]
  have hmeanU : ((Lucas.poolTotal n : ℝ)/N)/X ≤
      (fwMeanB (2*u)/2 + c + c + fwMeanB u/W)/(u*q) := by
    have he := hce.2.2.2.1
    have ht := hce.2.2.2.2.2
    rw [hEB] at ht
    have hid : (fwMeanB (2*u)/2 + c + c + fwMeanB u/W)/(u*q) =
      (fwMeanB (2*u)/2)/(u*q) + 2*c/(u*q) + (fwMeanB u/W)/(u*q) := by ring
    rw [hid]
    linarith [hm.2]
  exact ⟨huq, hcntL, hcntU, hmeanL, hmeanU⟩

end
end Sude
