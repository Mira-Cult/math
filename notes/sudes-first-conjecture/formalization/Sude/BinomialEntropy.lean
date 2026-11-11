import Sude.FC2KEntropyCurvature

/-! Binomial entropy bounds derived from the finite binomial expansion. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- Any individual term in the binomial distribution has mass at most one.
No stochastic independence assumption is used here. -/
theorem binomial_term_le_one (m k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hk : k ≤ m) :
    (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) ≤ 1 := by
  have hsum := Finset.single_le_sum (s := Finset.range (m + 1))
    (f := fun i => p ^ i * (1 - p) ^ (m - i) * (m.choose i : ℝ))
    (fun i _ => mul_nonneg (mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)) (by positivity))
    (show k ∈ Finset.range (m + 1) by simp; omega)
  have hexp := add_pow p (1 - p) m
  have hone : (p + (1 - p)) ^ m = (1 : ℝ) := by ring_nf
  rw [hone] at hexp
  rw [← hexp] at hsum
  nlinarith

/-- The standard entropy upper bound for an interior binomial coefficient.
The endpoints are handled separately by their exact coefficient values. -/
theorem binomial_choose_le_exp_entropy {m k : ℕ} (hk0 : 0 < k) (hkm : k < m) :
    (m.choose k : ℝ) ≤ Real.exp ((m : ℝ) * Real.binEntropy ((k : ℝ) / m)) := by
  let p : ℝ := (k : ℝ) / m
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hk : (0 : ℝ) < k := by exact_mod_cast hk0
  have hkm' : (k : ℝ) < m := by exact_mod_cast hkm
  have hp0 : 0 < p := div_pos hk hm
  have hp1 : p < 1 := (div_lt_one hm).2 hkm'
  have hr : 0 < p ^ k * (1 - p) ^ (m - k) :=
    mul_pos (pow_pos hp0 _) (pow_pos (by linarith) _)
  have hterm := binomial_term_le_one m k p hp0.le hp1.le (by omega)
  have hlog : (m : ℝ) * Real.binEntropy p =
      -Real.log (p ^ k * (1 - p) ^ (m - k)) := by
    rw [Real.binEntropy, Real.log_inv, Real.log_inv, Real.log_mul (ne_of_gt (pow_pos hp0 _))
      (ne_of_gt (pow_pos (by linarith : 0 < 1 - p) _)), Real.log_pow, Real.log_pow]
    have hmk : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := by exact Nat.cast_sub (by omega : k ≤ m)
    rw [hmk]
    dsimp [p]
    field_simp
    ring
  rw [hlog, Real.exp_neg, Real.exp_log hr]
  rw [← one_div]
  apply (le_div_iff₀ hr).2
  nlinarith

/-- Entropy upper bound including the endpoint cases `k = 0` and `k = m`. -/
theorem binomial_choose_le_exp_entropy_all {m k : ℕ} (hk : k ≤ m) :
    (m.choose k : ℝ) ≤ Real.exp ((m : ℝ) * Real.binEntropy ((k : ℝ) / m)) := by
  by_cases hk0 : k = 0
  · subst k
    simp
  by_cases hkm : k = m
  · subst k
    have hm : (m : ℝ) ≠ 0 := by exact_mod_cast hk0
    simp [hm]
  exact binomial_choose_le_exp_entropy (Nat.pos_of_ne_zero hk0) (lt_of_le_of_ne hk hkm)

/-- The exact finite lower-binomial-tail estimate used for small cuts. For
`0 ≤ z ≤ 1`, multiplying the unweighted tail by `z^r` is dominated by the
full binomial expansion. This includes `r = 0` and `z = 0`. -/
theorem binomial_lower_tail_weighted (m r : ℕ) (z : ℝ)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hr : r ≤ m) :
    (∑ k ∈ Finset.range (r + 1), (m.choose k : ℝ)) * z ^ r ≤ (1 + z) ^ m := by
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ k ∈ Finset.range (r + 1), (m.choose k : ℝ) * z ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkr : k ≤ r := by simpa using Finset.mem_range.mp hk
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hz0 hz1 hkr) (by positivity)
    _ ≤ ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * z ^ k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (by omega)
      · intro k hk hk'
        exact mul_nonneg (by positivity) (pow_nonneg hz0 _)
    _ = (z + 1) ^ m := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [one_pow, mul_one]
      ring
    _ = (1 + z) ^ m := by rw [add_comm]

/-- Entropy bound for an integer lower tail at a real threshold. The threshold
need not be an integer multiple of `m`. -/
theorem binomial_lower_tail_le_exp_entropy (m r : ℕ) (a : ℝ)
    (ha0 : 0 < a) (ha : a ≤ 1 / 2) (hr : r ≤ m)
    (hthreshold : (r : ℝ) ≤ m * a) :
    (∑ k ∈ Finset.range (r + 1), (m.choose k : ℝ)) ≤
      Real.exp ((m : ℝ) * Real.binEntropy a) := by
  let z := a / (1 - a)
  have hden : 0 < 1 - a := by linarith
  have hz0 : 0 < z := div_pos ha0 hden
  have hz1 : z ≤ 1 := by
    dsimp [z]
    apply (div_le_one hden).2
    linarith
  have hlogz : Real.log z ≤ 0 := Real.log_nonpos hz0.le hz1
  have hweighted := binomial_lower_tail_weighted m r z hz0.le hz1 hr
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range (r + 1), (m.choose k : ℝ) := by positivity
  have hexpbound : Real.exp (((m : ℝ) * a) * Real.log z) ≤ z ^ r := by
    have h := mul_le_mul_of_nonpos_right hthreshold hlogz
    apply (Real.exp_le_exp).2 at h
    rw [Real.exp_nat_mul, Real.exp_log hz0] at h
    exact h
  have hproduct : (∑ k ∈ Finset.range (r + 1), (m.choose k : ℝ)) *
      Real.exp (((m : ℝ) * a) * Real.log z) ≤ (1 + z) ^ m :=
    (mul_le_mul_of_nonneg_left hexpbound hsum0).trans hweighted
  have hlogid : Real.log (1 + z) - a * Real.log z = Real.binEntropy a := by
    have hsum : 1 + z = (1 - a)⁻¹ := by dsimp [z]; field_simp; ring
    rw [hsum, Real.log_inv, show z = a / (1 - a) by rfl,
      Real.log_div (ne_of_gt ha0) (ne_of_gt hden), Real.binEntropy, Real.log_inv, Real.log_inv]
    ring
  have hnum : (1 + z) ^ m = Real.exp ((m : ℝ) * Real.log (1 + z)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith : 0 < 1 + z)]
  have hbound := (le_div_iff₀ (Real.exp_pos (((m : ℝ) * a) * Real.log z))).2 hproduct
  rw [hnum, ← Real.exp_sub] at hbound
  have heq : (m : ℝ) * Real.log (1 + z) - ((m : ℝ) * a) * Real.log z =
      (m : ℝ) * Real.binEntropy a := by rw [← hlogid]; ring
  rw [heq] at hbound
  exact hbound

/-- FC2K's small-cut exception count, with the exact nonintegral threshold
`199*s/400` represented by an integer inequality. -/
theorem fc2k_exception_binomial_bound (s r : ℕ) (hr : 400 * r ≤ 199 * s) :
    (∑ k ∈ Finset.range (r + 1), ((3 * s).choose k : ℝ)) ≤
      Real.exp ((3 * s : ℕ) * Real.binEntropy ((199 : ℝ) / 1200)) := by
  apply binomial_lower_tail_le_exp_entropy (3 * s) r (199 / 1200)
    (by norm_num) (by norm_num) (by omega)
  have hreal : (400 : ℝ) * r ≤ 199 * s := by exact_mod_cast hr
  push_cast
  linarith

end
end Sude
