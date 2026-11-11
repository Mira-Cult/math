import Sude.APInterval
import Sude.FinitePrefixPoolBound

/-! Upper prime counts from the existing published theta and index bounds. -/
namespace Sude
noncomputable section

/-- Every prime in (b,c] has logarithmic weight at least log b. -/
theorem count_log_le_thetaAP_interval (b c : ℝ) (q : ℕ) (a : ℤ)
    (hb : 0 < b) (hbc : b ≤ c) :
    ((apInterval b c q a).card : ℝ) * Real.log b ≤ thetaAP c q a - thetaAP b q a := by
  rw [thetaAP_sub_eq_interval_sum b c q a hbc]
  calc
    ((apInterval b c q a).card : ℝ) * Real.log b =
        ∑ _p ∈ apInterval b c q a, Real.log b := by simp
    _ ≤ ∑ p ∈ apInterval b c q a, Real.log p := by
      apply Finset.sum_le_sum
      intro p hp
      have h := (mem_apInterval_iff b c q a (le_of_lt hb) (le_trans (le_of_lt hb) hbc) p).mp hp
      exact Real.log_le_log hb (le_of_lt h.2.1)

/-- BMOR's q=1 theta estimate gives a rigorous upper bound for a finite
interval's actual prime count, with a caller-supplied square-root enclosure. -/
theorem bmor_prime_interval_upper (bmor : BMORFiniteTheta) (b c L U : ℝ)
    (hb : 1 ≤ b) (hbc : b ≤ c) (hcap : c ≤ 10 ^ 12)
    (hL : L ≤ Real.log b) (hU : Real.sqrt c ≤ U) :
    L * (apInterval b c 1 0).card ≤ c - b + (518 / 125 : ℝ) * U := by
  have hlimit : (bmorLimit 1 : ℝ) = 10 ^ 12 := by norm_num [bmorLimit, bmorBaseLimit]
  have hblimit : b ≤ (bmorLimit 1 : ℝ) := by rw [hlimit]; exact le_trans hbc hcap
  have hclimit : c ≤ (bmorLimit 1 : ℝ) := by rw [hlimit]; exact hcap
  have hbtheta := bmor_theta_pointwise bmor 1 0 b (by decide) (by norm_num) (by decide) hb hblimit
  have hctheta := bmor_theta_pointwise bmor 1 0 c (by decide) (by norm_num) (by decide)
    (le_trans hb hbc) hclimit
  have hb' := (abs_le.mp hbtheta).1
  have hc' := (abs_le.mp hctheta).2
  simp only [Nat.totient_one, Nat.cast_one, div_one] at hb' hc'
  have hsqrt : Real.sqrt b ≤ U := le_trans (Real.sqrt_le_sqrt hbc) hU
  have hweight := count_log_le_thetaAP_interval b c 1 0 (by linarith) hbc
  have hscaled := mul_le_mul_of_nonneg_right hL (show (0 : ℝ) ≤ (apInterval b c 1 0).card by positivity)
  nlinarith

/-- The all-prime prefix agrees exactly with Nat.count's strict endpoint. -/
theorem apPrefix_one_card (N : ℕ) :
    (apPrefix (N : ℝ) 1 0).card = Nat.count Nat.Prime (N + 1) := by
  classical
  rw [Nat.count_eq_card_filter_range]
  simp [apPrefix]

/-- Adjacent closed-prefix and half-open-interval counts add exactly. -/
theorem prime_count_split (A B : ℕ) (hAB : A ≤ B) :
    Nat.count Nat.Prime (B + 1) = Nat.count Nat.Prime (A + 1) +
      (apInterval A B 1 0).card := by
  have ha : (0 : ℝ) ≤ A := by positivity
  have hb : (0 : ℝ) ≤ B := by positivity
  have hab : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hdisj : Disjoint (apPrefix (A : ℝ) 1 0) (apInterval A B 1 0) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := (mem_apPrefix_iff A 1 0 ha p).mp hp
    have hq' := (mem_apInterval_iff A B 1 0 ha hb p).mp hq
    linarith
  have hunion : apPrefix (A : ℝ) 1 0 ∪ apInterval A B 1 0 = apPrefix B 1 0 := by
    ext p
    rw [Finset.mem_union, mem_apPrefix_iff A 1 0 ha p, mem_apInterval_iff A B 1 0 ha hb p,
      mem_apPrefix_iff B 1 0 hb p]
    constructor
    · rintro (⟨hp, hpa, hmod⟩ | ⟨hp, _, hpb, hmod⟩)
      · exact ⟨hp, le_trans hpa hab, hmod⟩
      · exact ⟨hp, hpb, hmod⟩
    · rintro ⟨hp, hpb, hmod⟩
      by_cases hpa : (p : ℝ) ≤ A
      · exact Or.inl ⟨hp, hpa, hmod⟩
      · exact Or.inr ⟨hp, lt_of_not_ge hpa, hpb, hmod⟩
  have hc := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj, apPrefix_one_card, apPrefix_one_card] at hc
  exact hc.symm

/-- A rational log enclosure obtained from the proved inequality for
log(1+u) and the library's explicit lower bound for log 2. -/
theorem log_scaled_rational_lower (u : ℝ) (k : ℕ) (hu : 0 ≤ u) :
    (k : ℝ) * Real.log 2 + 2 * u / (u + 2) ≤ Real.log ((1 + u) * 2 ^ k) := by
  have h := Real.le_log_one_add_of_nonneg hu
  rw [Real.log_mul (by linarith : (1 + u) ≠ 0) (by positivity : (2 : ℝ) ^ k ≠ 0),
    Real.log_pow]
  linarith

theorem log_3333334_gt_fifteen : (15 : ℝ) < Real.log 3333334 := by
  have h := log_scaled_rational_lower (7 / 12) 21 (by norm_num)
  have hscale : (1 + 7 / 12 : ℝ) * 2 ^ 21 ≤ 3333334 := by norm_num
  have hm := Real.log_le_log (by positivity : (0 : ℝ) < (1 + 7 / 12) * 2 ^ 21) hscale
  have ht := Real.log_two_gt_d9
  norm_num at h ht ⊢
  linarith

theorem log_50000000_lower : (177 / 10 : ℝ) ≤ Real.log 50000000 := by
  have h := log_scaled_rational_lower (19 / 40) 25 (by norm_num)
  have hscale : (1 + 19 / 40 : ℝ) * 2 ^ 25 ≤ 50000000 := by norm_num
  have hm := Real.log_le_log (by positivity : (0 : ℝ) < (1 + 19 / 40) * 2 ^ 25) hscale
  have ht := Real.log_two_gt_d9
  norm_num at h ht ⊢
  linarith

theorem log_75000000_lower : (18 : ℝ) ≤ Real.log 75000000 := by
  have h := log_scaled_rational_lower (11 / 100) 26 (by norm_num)
  have hscale : (1 + 11 / 100 : ℝ) * 2 ^ 26 ≤ 75000000 := by norm_num
  have hm := Real.log_le_log (by positivity : (0 : ℝ) < (1 + 11 / 100) * 2 ^ 26) hscale
  have ht := Real.log_two_gt_d9
  norm_num at h ht ⊢
  linarith

theorem log_150000000_lower : (94 / 5 : ℝ) ≤ Real.log 150000000 := by
  have h := log_scaled_rational_lower (11 / 100) 27 (by norm_num)
  have hscale : (1 + 11 / 100 : ℝ) * 2 ^ 27 ≤ 150000000 := by norm_num
  have hm := Real.log_le_log (by positivity : (0 : ℝ) < (1 + 11 / 100) * 2 ^ 27) hscale
  have ht := Real.log_two_gt_d9
  norm_num at h ht ⊢
  linarith

theorem log_300000000_lower : (39 / 2 : ℝ) ≤ Real.log 300000000 := by
  have h := log_scaled_rational_lower (11 / 100) 28 (by norm_num)
  have hscale : (1 + 11 / 100 : ℝ) * 2 ^ 28 ≤ 300000000 := by norm_num
  have hm := Real.log_le_log (by positivity : (0 : ℝ) < (1 + 11 / 100) * 2 ^ 28) hscale
  have ht := Real.log_two_gt_d9
  norm_num at h ht ⊢
  linarith

/-- A lower bound for the K-th prime gives an upper bound for every prime
at or below A, with the one-based index handled explicitly. -/
theorem prime_count_lt_of_rs_index (lower : RSIndexLower) (A K : ℕ) (hK : 1 ≤ K)
    (hnum : (A : ℝ) < (K : ℝ) * Real.log K) :
    Nat.count Nat.Prime (A + 1) < K := by
  have hp : A < primeOneBased K := by
    exact_mod_cast lt_trans hnum (lower K hK)
  have hnth : A + 1 ≤ Nat.nth Nat.Prime (K - 1) := by
    change A < Nat.nth Nat.Prime (K - 1) at hp
    omega
  have hc := Nat.le_nth_of_count_le hnth
  omega

theorem prime_count_50000000_upper (lower : RSIndexLower) :
    Nat.count Nat.Prime (50000000 + 1) < 3333334 := by
  apply prime_count_lt_of_rs_index lower 50000000 3333334 (by norm_num)
  have h := log_3333334_gt_fifteen
  norm_num at h ⊢
  nlinarith

theorem prime_count_75000000_upper (lower : RSIndexLower) :
    Nat.count Nat.Prime (75000000 + 1) < 5000000 := by
  apply prime_count_lt_of_rs_index lower 75000000 5000000 (by norm_num)
  have h := log_3333334_gt_fifteen
  have hm : Real.log (3333334 : ℝ) ≤ Real.log 5000000 :=
    Real.log_le_log (by norm_num) (by norm_num)
  norm_num at h ⊢
  nlinarith

theorem interval_50000000_150000000_upper (bmor : BMORFiniteTheta) :
    (apInterval 50000000 150000000 1 0).card < 5653000 := by
  have h := bmor_prime_interval_upper bmor 50000000 150000000 (177 / 10) 12500
    (by norm_num) (by norm_num) (by norm_num) log_50000000_lower
    (Real.sqrt_le_iff.mpr (by norm_num))
  have hr : ((apInterval 50000000 150000000 1 0).card : ℝ) < 5653000 := by
    norm_num at h
    linarith
  exact_mod_cast hr

theorem interval_75000000_150000000_upper (bmor : BMORFiniteTheta) :
    (apInterval 75000000 150000000 1 0).card < 4173000 := by
  have h := bmor_prime_interval_upper bmor 75000000 150000000 18 25000
    (by norm_num) (by norm_num) (by norm_num) log_75000000_lower
    (Real.sqrt_le_iff.mpr (by norm_num))
  have hr : ((apInterval 75000000 150000000 1 0).card : ℝ) < 4173000 := by
    norm_num at h
    linarith
  exact_mod_cast hr

theorem interval_150000000_300000000_upper (bmor : BMORFiniteTheta) :
    (apInterval 150000000 300000000 1 0).card < 7985000 := by
  have h := bmor_prime_interval_upper bmor 150000000 300000000 (94 / 5) 25000
    (by norm_num) (by norm_num) (by norm_num) log_150000000_lower
    (Real.sqrt_le_iff.mpr (by norm_num))
  have hr : ((apInterval 150000000 300000000 1 0).card : ℝ) < 7985000 := by
    norm_num at h
    linarith
  exact_mod_cast hr

theorem interval_300000000_450000000_upper (bmor : BMORFiniteTheta) :
    (apInterval 300000000 450000000 1 0).card < 7699000 := by
  have h := bmor_prime_interval_upper bmor 300000000 450000000 (39 / 2) 25000
    (by norm_num) (by norm_num) (by norm_num) log_300000000_lower
    (Real.sqrt_le_iff.mpr (by norm_num))
  have hr : ((apInterval 300000000 450000000 1 0).card : ℝ) < 7699000 := by
    norm_num at h
    linarith
  exact_mod_cast hr

/-- The two previously unresolved FPF endpoint bounds follow from the
published RS and BMOR assumptions, with no finite prime-count oracle. -/
theorem prime_count_150000000_upper (lower : RSIndexLower) (bmor : BMORFiniteTheta) :
    Nat.count Nat.Prime (150000000 + 1) < 3000 * 3000 := by
  have hsplit := prime_count_split 50000000 150000000 (by norm_num)
  have h0 := prime_count_50000000_upper lower
  have h1 := interval_50000000_150000000_upper bmor
  norm_num at hsplit h0 h1 ⊢
  omega

theorem prime_count_450000000_upper (lower : RSIndexLower) (bmor : BMORFiniteTheta) :
    Nat.count Nat.Prime (450000000 + 1) < 5000 * 5000 := by
  have hsplit₁ := prime_count_split 75000000 150000000 (by norm_num)
  have hsplit₂ := prime_count_split 150000000 300000000 (by norm_num)
  have hsplit₃ := prime_count_split 300000000 450000000 (by norm_num)
  have h0 := prime_count_75000000_upper lower
  have h1 := interval_75000000_150000000_upper bmor
  have h2 := interval_150000000_300000000_upper bmor
  have h3 := interval_300000000_450000000_upper bmor
  norm_num at hsplit₁ hsplit₂ hsplit₃ h0 h1 h2 h3 ⊢
  omega

theorem poolMaximum_gt_of_count_le {n B : ℕ}
    (hcount : Nat.count Nat.Prime (B + 1) ≤ n * n) : B < poolMaximum n := by
  have h := (Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime).mp hcount
  change B + 1 ≤ poolMaximum n at h
  omega

theorem finitePrefix_M_below_poolMaximum (lower : RSIndexLower) (bmor : BMORFiniteTheta)
    {n : ℕ} (hn : 3000 ≤ n) : 150000000 < poolMaximum n := by
  apply poolMaximum_gt_of_count_le
  have hcount := prime_count_150000000_upper lower bmor
  have hs : 3000 * 3000 ≤ n * n := Nat.mul_self_le_mul_self hn
  omega

theorem finitePrefix_H_below_poolMaximum (lower : RSIndexLower) (bmor : BMORFiniteTheta)
    {n : ℕ} (hn : 5000 ≤ n) : 450000000 < poolMaximum n := by
  apply poolMaximum_gt_of_count_le
  have hcount := prime_count_450000000_upper lower bmor
  have hs : 5000 * 5000 ≤ n * n := Nat.mul_self_le_mul_self hn
  omega

theorem finitePrefix_M_prime_in_pool (lower : RSIndexLower) (bmor : BMORFiniteTheta)
    {n p : ℕ} (hn : 3000 ≤ n) (hp : Nat.Prime p) (hne : p ≠ 2)
    (hpmax : p ≤ 150000000) : p ∈ pool n :=
  prime_mem_pool_of_le_max hp hne (le_trans hpmax (finitePrefix_M_below_poolMaximum lower bmor hn).le)

theorem finitePrefix_H_prime_in_pool (lower : RSIndexLower) (bmor : BMORFiniteTheta)
    {n p : ℕ} (hn : 5000 ≤ n) (hp : Nat.Prime p) (hne : p ≠ 2)
    (hpmax : p ≤ 450000000) : p ∈ pool n :=
  prime_mem_pool_of_le_max hp hne (le_trans hpmax (finitePrefix_H_below_poolMaximum lower bmor hn).le)

end
end Sude
