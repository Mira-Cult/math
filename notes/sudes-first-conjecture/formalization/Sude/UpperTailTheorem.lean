import Sude.UpperTailWideAndMod
import Sude.UpperTailTargets
import Sude.CYDiagonalWidenedCompletion
import Sude.CentralPostInputs
import Sude.DiagonalLineTransfer
import Sude.PrefixInstalledNetwork
import Sude.PermutationExceptions
import Sude.PhysicalCutRouting
import Sude.TargetRouting
import Sude.ActiveRectangleDiagonalGeometry
import Sude.PrefixDeterministicFourWeight

/-!
# Complete Upper-Tail Proof of Sude's First Theorem (`n ≥ 35,735`)

Assembles the full upper-tail proof `Sude.upper_tail_hasSquare` for every odd `n ≥ 35,735`
from the published analytic inputs (`BMORFiniteTheta`, `BMORExplicitFormulaImports`,
`MVBrunTitchmarsh`, and Rosser–Schoenfeld bounds):

1. **Section 1 (`upper_tail_t75_targets_1400`)**: Sharpens the T75 prime target supply to
   `D = y / 1400` across all odd `n ≥ 35,735` using `apInterval_mod_two_card_lower_ge_2e10`
   and `apInterval_filter_mod_two_prime_sharp`.
2. **Section 2 (`ut_central_band_sharp_completion`)**: Unbounded central-band diagonal and
   off-diagonal completion at `ε = 15 / 10000` using Keepout `(0.355 * X, 0.578 * X]`
   separation (`0` prior deletions) and `apInterval_mod_two_card_lower_ge_1e9`.
3. **Section 3 (`upper_tail_hasSquare`)**: Jointly installs rectangles and two expanding
   ordinary permutation networks, balances Growth midpoints across all `2 * n` rows and columns
   simultaneously via `prefix_deterministic_stage_assignment_four`, completes the central cells,
   centers and routes exact integer flows via `twoNetworks_realize_bounded_integer_flows_of_evenIntervalGrid`,
   and repairs both diagonals to a common prime via `packed_prime_diagonal_repair_of_evenIntervalGrid`.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

/-! ## Section 1: Sharpened Upper-Tail T75 Prime Target Supply (`D = y / 1400`) -/

/-- For every odd `n ≥ 35,735`, there exists an odd prime target vector `f : Fin n → ℕ`
of exact sum `Lucas.poolTotal n` with `|(f i : ℝ) - y| ≤ y / 1400`. -/
theorem upper_tail_t75_targets_1400
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports) (rs : RSPrimeCountImports)
    (hMV : MVBrunTitchmarsh) (sharp : RSIndexLowerSharp) (hRS_hi : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) (hn_odd : Odd n) :
    let y : ℝ := (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let D : ℝ := y / 1400
    ∃ f : Fin n → ℕ,
      (∑ i, f i) = Lucas.poolTotal n ∧
      (∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ) - y| ≤ D) := by
  dsimp only
  have hn_pos : 0 < n := by omega
  let Xnat := poolMaximum n
  let X : ℝ := Xnat
  let y : ℝ := (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue
  let D : ℝ := y / 1400
  obtain ⟨hX_lo_n2, hX_gt_283, hX_lt_n3, hlogX_gt, hlogX_lt⟩ :=
    poolMaximum_bounds_ge_35735 sharp hRS_hi hn
  obtain ⟨hlogn_gt, hlogn3, hlogn4⟩ := log_nat_pow_bounds_ge_35735 hn
  have hXpos : 0 < X := by linarith
  have hm_bounds := global_pool_mean_bounds rs sharp (by omega : 2001 ≤ n)
  have hm_lo : (449 / 1000 : ℝ) * X < centralEntriesMean (prescribedPoolValues n) centralPoolValue := by
    rw [prescribedPoolValues_mean]
    exact (lt_div_iff₀ hXpos).mp hm_bounds.1
  have hm_hi : centralEntriesMean (prescribedPoolValues n) centralPoolValue < (519 / 1000 : ℝ) * X := by
    rw [prescribedPoolValues_mean]
    exact (div_lt_iff₀ hXpos).mp hm_bounds.2
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hy_lo : (35735 : ℝ) * ((449 / 1000 : ℝ) * (283 * 10 ^ 8 : ℝ)) ≤ y := by
    have hm1 : (449 / 1000 : ℝ) * (283 * 10 ^ 8 : ℝ) ≤
        centralEntriesMean (prescribedPoolValues n) centralPoolValue := by linarith
    dsimp [y]
    exact mul_le_mul hnR hm1 (by positivity) hn_nonneg
  have hy_gt : (45 * 10 ^ 13 : ℝ) < y := by linarith
  have hD_gt : (3 * 10 ^ 11 : ℝ) < D := by dsimp [D]; linarith
  have hD_pos : 0 < D := by linarith
  have hy_eq : y = 1400 * D := by dsimp [D]; ring
  have hyD_lt_n4 : y + D < (n : ℝ) ^ 4 := by
    have hy1 : y < (n : ℝ) * ((519 / 1000 : ℝ) * X) := by
      dsimp [y]
      exact mul_lt_mul_of_pos_left hm_hi (by linarith)
    have hy2 : (n : ℝ) * ((519 / 1000 : ℝ) * X) < (n : ℝ) * ((519 / 1000 : ℝ) * (n : ℝ) ^ 3) :=
      mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hX_lt_n3 (by norm_num)) (by linarith)
    have hy3 : (n : ℝ) * ((519 / 1000 : ℝ) * (n : ℝ) ^ 3) = (519 / 1000 : ℝ) * (n : ℝ) ^ 4 := by ring
    have hn4_pos : 0 < (n : ℝ) ^ 4 := by positivity
    dsimp [D]
    linarith
  have hlog_yD : Real.log (y + D) ≤ 4 * Real.log (n : ℝ) := by
    have h1 := Real.log_le_log (by linarith) hyD_lt_n4.le
    rw [Real.log_pow] at h1
    push_cast at h1
    exact h1
  let Ln : ℕ := ⌈Real.log (n : ℝ)⌉₊
  have hLn_ge : Real.log (n : ℝ) ≤ (Ln : ℝ) := Nat.le_ceil _
  have hLn_lt : (Ln : ℝ) < Real.log (n : ℝ) + 1 := Nat.ceil_lt_add_one (by linarith)
  have hLn_11 : 11 ≤ Ln := by
    have : (10 : ℝ) < (Ln : ℝ) := lt_of_lt_of_le hlogn_gt hLn_ge
    exact_mod_cast this
  have hLn_ratio : (Ln : ℝ) ≤ (11 / 10 : ℝ) * Real.log (n : ℝ) := by linarith
  let C : ℕ := 3 * Ln
  let H0 : ℕ := 3 * Ln
  let k : ℕ := 6 * Ln
  have hC_ge : 1 ≤ C := by omega
  have hlog_sq_100 : (100 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
    have hm := mul_le_mul hlogn_gt.le hlogn_gt.le (by norm_num) (by linarith)
    linarith
  have hlog2_le : 223 * (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) := by
    have hmul : 100 * (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ 4 := by
      calc 100 * (Real.log (n : ℝ)) ^ 2
          ≤ (Real.log (n : ℝ)) ^ 2 * (Real.log (n : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hlog_sq_100 (sq_nonneg _)
        _ = (Real.log (n : ℝ)) ^ 4 := by ring
    linarith [hlogn4]
  have hLn2_le : (Ln : ℝ) ^ 2 ≤ (121 / 100 : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
    have hm := mul_le_mul hLn_ratio hLn_ratio (by positivity) (by positivity)
    linarith
  have hLn1_le : (Ln : ℝ) ≤ (11 / 100 : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
    have hm := mul_le_mul hlogn_gt.le hLn_ratio (by positivity) (by linarith)
    linarith
  have hD_ge_nX : (n : ℝ) * X ≤ 3500 * D := by
    have hm := mul_le_mul_of_nonneg_left hm_lo.le hn_nonneg
    dsimp [D, y]
    linarith
  have hnX_ge : (283 * 10 ^ 8 : ℝ) * (n : ℝ) ≤ (n : ℝ) * X := by
    have hm := mul_le_mul_of_nonneg_left hX_gt_283.le hn_nonneg
    linarith
  have hn_lt_D : 2000000 * (n : ℝ) ≤ D := by linarith
  have hsize_le : 2 * (2 * C + 4 * C * k + (H0 + 6) * C + H0) + H0 + 4 ≤ n := by
    have h1_le : (1 : ℝ) ≤ (1 / 100 : ℝ) * (Real.log (n : ℝ)) ^ 2 := by linarith
    have hreal : ((2 * (2 * C + 4 * C * k + (H0 + 6) * C + H0) + H0 + 4 : ℕ) : ℝ) ≤ (n : ℝ) := by
      dsimp [C, H0, k]
      push_cast
      linarith
    exact_mod_cast hreal
  obtain ⟨p_lo, hplo_prime, hplo_odd, hplo_lo, hplo_hi⟩ :=
    odd_prime_in_interval_all_scales bmor imp (lo := y - D) (hi := y - D / 2)
      (by linarith) (by linarith) (by linarith)
  obtain ⟨p_hi, hphi_prime, hphi_odd, hphi_lo, hphi_hi⟩ :=
    odd_prime_in_interval_all_scales bmor imp (lo := y + D / 2) (hi := y + D)
      (by linarith) (by linarith) (by linarith)
  let b_mid : ℝ := y - D / 4
  let c_mid : ℝ := y + D / 4
  let P_mid := apInterval b_mid c_mid 2 1
  have hb_mid_gt : (44 * 10 ^ 13 : ℝ) < b_mid := by dsimp [b_mid]; linarith
  have hlog_b_mid_gt : 30 < Real.log b_mid := by
    have h2_48 : (2 : ℝ) ^ 48 < b_mid := by linarith
    have hlog := Real.log_lt_log (by positivity) h2_48
    rw [Real.log_pow] at hlog
    push_cast at hlog
    linarith [Real.log_two_gt_d9]
  have hlog_c_le_b : Real.log c_mid ≤ (31 / 30 : ℝ) * Real.log b_mid := by
    have hc_le_2b : c_mid ≤ 2 * b_mid := by dsimp [b_mid, c_mid]; linarith
    have hc_pos : 0 < c_mid := by dsimp [c_mid]; linarith
    have hb_ne : b_mid ≠ 0 := ne_of_gt (by linarith : 0 < b_mid)
    have h1 := Real.log_le_log hc_pos hc_le_2b
    rw [Real.log_mul (by norm_num) hb_ne] at h1
    linarith [Real.log_two_lt_d9]
  have hlog_c_le_Ln : Real.log c_mid ≤ 4 * (Ln : ℝ) := by
    have h1 : Real.log c_mid ≤ Real.log (y + D) :=
      Real.log_le_log (by dsimp [c_mid]; linarith) (by dsimp [c_mid]; linarith)
    linarith
  have hP_mid_card_log : (23 / 60 : ℝ) * D ≤ (P_mid.card : ℝ) * Real.log c_mid := by
    have h := (div_le_iff₀ (Real.log_pos (by dsimp [c_mid]; linarith))).mp
      (apInterval_mod_two_card_lower_ge_2e10 bmor imp (b := b_mid) (c := c_mid) (X := c_mid)
        (by linarith) (by dsimp [b_mid, c_mid]; linarith) (le_refl _))
    have hba : (c_mid - b_mid) - (b_mid + c_mid) / 24000 = (23 / 60 : ℝ) * D := by
      dsimp [b_mid, c_mid]; rw [hy_eq]; ring
    linarith
  have hP_mid_card_Ln : (23 / 60 : ℝ) * D ≤ (P_mid.card : ℝ) * (4 * (Ln : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_left hlog_c_le_Ln (Nat.cast_nonneg P_mid.card)
    linarith
  have hP_mid_props : ∀ p ∈ P_mid, Nat.Prime p ∧ Odd p ∧ b_mid < (p : ℝ) ∧ (p : ℝ) ≤ c_mid := by
    intro p hp
    have ⟨hp_prime, hlo, hhi, hmod⟩ :=
      (mem_apInterval_iff b_mid c_mid 2 1 (by linarith) (by dsimp [b_mid, c_mid]; linarith) p).mp hp
    have hp_odd : Odd p := by rw [Nat.odd_iff]; exact_mod_cast hmod
    exact ⟨hp_prime, hp_odd, hlo, hhi⟩
  let u_nat : ℕ := ⌊b_mid⌋₊
  let K_bins : ℕ := ⌊(D / 2) / ((2 * H0 : ℕ) : ℝ)⌋₊ + 2
  have hbin_range : ∀ p ∈ P_mid, (p - u_nat) / (2 * H0) < K_bins := by
    intro p hp
    have hp_p := hP_mid_props p hp
    have hu_le : (u_nat : ℝ) ≤ b_mid := Nat.floor_le (by linarith)
    have hu_gt : b_mid - 1 < (u_nat : ℝ) := Nat.sub_one_lt_floor b_mid
    have hp_ge_u : u_nat ≤ p := by
      have : (u_nat : ℝ) ≤ (p : ℝ) := by linarith [hp_p.2.2.1]
      exact_mod_cast this
    have hdiff_le : ((p - u_nat : ℕ) : ℝ) ≤ D / 2 + 1 := by
      rw [Nat.cast_sub hp_ge_u]
      dsimp [b_mid, c_mid] at hp_p hu_gt
      linarith [hp_p.2.2.2]
    have h2H0_pos : (0 : ℝ) < ((2 * H0 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * H0)
    have h2H0_ge_1 : (1 : ℝ) ≤ ((2 * H0 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * H0)
    let q_bin := (p - u_nat) / (2 * H0)
    have hq_mul : q_bin * (2 * H0) ≤ p - u_nat := Nat.div_mul_le_self _ _
    have hq_real : (q_bin : ℝ) * ((2 * H0 : ℕ) : ℝ) ≤ D / 2 + ((2 * H0 : ℕ) : ℝ) := by
      have hc : ((q_bin * (2 * H0) : ℕ) : ℝ) ≤ ((p - u_nat : ℕ) : ℝ) := Nat.cast_le.mpr hq_mul
      rw [Nat.cast_mul] at hc
      linarith
    have hq_div : (q_bin : ℝ) ≤ (D / 2) / ((2 * H0 : ℕ) : ℝ) + 1 := by
      rw [div_add_one h2H0_pos.ne', le_div_iff₀ h2H0_pos]
      exact hq_real
    have hq_fl : q_bin ≤ ⌊(D / 2) / ((2 * H0 : ℕ) : ℝ)⌋₊ + 1 := by
      have h1 : ⌊(q_bin : ℝ)⌋₊ ≤ ⌊(D / 2) / ((2 * H0 : ℕ) : ℝ) + 1⌋₊ := Nat.floor_mono hq_div
      rw [Nat.floor_natCast, Nat.floor_add_one (by positivity)] at h1
      exact h1
    dsimp [K_bins]
    omega
  have hK_lt_P_mid : K_bins < P_mid.card := by
    have hfl : ((⌊(D / 2) / ((2 * H0 : ℕ) : ℝ)⌋₊ : ℕ) : ℝ) ≤ (D / 2) / ((2 * H0 : ℕ) : ℝ) :=
      Nat.floor_le (by positivity)
    have h2H0_eq : ((2 * H0 : ℕ) : ℝ) = 6 * (Ln : ℝ) := by dsimp [H0]; push_cast; ring
    have hLn_pos : (0 : ℝ) < (Ln : ℝ) := by positivity
    have hK_real : (K_bins : ℝ) * (4 * (Ln : ℝ)) < (23 / 60 : ℝ) * D := by
      dsimp [K_bins]
      rw [h2H0_eq] at hfl ⊢
      have hm := mul_le_mul_of_nonneg_right hfl (by positivity : (0 : ℝ) ≤ 6 * (Ln : ℝ))
      rw [div_mul_cancel₀ _ (by positivity)] at hm
      have hLn_D : (Ln : ℝ) < D / 1000 := by
        linarith [hLn1_le, hlog2_le, hn_lt_D]
      push_cast
      linarith
    have hlt_mul : (K_bins : ℝ) * (4 * (Ln : ℝ)) < (P_mid.card : ℝ) * (4 * (Ln : ℝ)) :=
      lt_of_lt_of_le hK_real hP_mid_card_Ln
    have hlt_real : (K_bins : ℝ) < (P_mid.card : ℝ) :=
      lt_of_mul_lt_mul_right hlt_mul (by positivity)
    exact_mod_cast hlt_real
  obtain ⟨r0, hr0_mem, r1, hr1_mem, hr0_lt_r1, hsame_bin⟩ :=
    exists_same_bin_pair_of_lt_card hbin_range hK_lt_P_mid
  have hr0_props := hP_mid_props r0 hr0_mem
  have hr1_props := hP_mid_props r1 hr1_mem
  have hu_le_r0 : u_nat ≤ r0 := by
    have hu_le : (u_nat : ℝ) ≤ b_mid := Nat.floor_le (by linarith)
    have : (u_nat : ℝ) ≤ (r0 : ℝ) := by linarith [hr0_props.2.2.1]
    exact_mod_cast this
  have hr1_sub_r0_lt : r1 - r0 < 2 * H0 := by
    let B := 2 * H0
    have hB_pos : 0 < B := by dsimp [B, H0]; omega
    have hd0 := Nat.div_add_mod (r0 - u_nat) B
    have hd1 := Nat.div_add_mod (r1 - u_nat) B
    have hmul_eq : B * ((r0 - u_nat) / B) = B * ((r1 - u_nat) / B) :=
      congrArg (B * ·) hsame_bin
    have hm0 : (r0 - u_nat) % B < B := Nat.mod_lt _ hB_pos
    have hm1 : (r1 - u_nat) % B < B := Nat.mod_lt _ hB_pos
    have hsub_eq : (r1 - r0) + (r0 - u_nat) = r1 - u_nat := by omega
    omega
  have hr1_sub_r0_even : 2 ∣ (r1 - r0) := by
    obtain ⟨m0, hm0⟩ := hr0_props.2.1
    obtain ⟨m1, hm1⟩ := hr1_props.2.1
    exact ⟨m1 - m0, by omega⟩
  let h0 : ℕ := (r1 - r0) / 2
  have hh0_pos : 0 < h0 := by
    obtain ⟨m, hm⟩ := hr1_sub_r0_even
    omega
  have hh0_le : h0 ≤ H0 := by omega
  have hr1_eq : r0 + 2 * h0 = r1 := by
    obtain ⟨m, hm⟩ := hr1_sub_r0_even
    dsimp [h0]; omega
  let b_cen : ℝ := y - D / 2
  let c_cen : ℝ := y + D / 2
  let P_cen := apInterval b_cen c_cen 2 1
  have hP_cen_props : ∀ p ∈ P_cen, Nat.Prime p ∧ Odd p ∧ b_cen < (p : ℝ) ∧ (p : ℝ) ≤ c_cen := by
    intro p hp
    have ⟨hp_prime, hlo, hhi, hmod⟩ :=
      (mem_apInterval_iff b_cen c_cen 2 1 (by dsimp [b_cen]; linarith)
        (by dsimp [b_cen, c_cen]; linarith) p).mp hp
    have hp_odd : Odd p := by rw [Nat.odd_iff]; exact_mod_cast hmod
    exact ⟨hp_prime, hp_odd, hlo, hhi⟩
  have hP_cen_card_Ln : (53 / 60 : ℝ) * D ≤ (P_cen.card : ℝ) * (4 * (Ln : ℝ)) := by
    have h := (div_le_iff₀ (Real.log_pos (by dsimp [c_cen]; linarith))).mp
      (apInterval_mod_two_card_lower_ge_2e10 bmor imp (b := b_cen) (c := c_cen) (X := c_cen)
        (by dsimp [b_cen]; linarith) (by dsimp [b_cen, c_cen]; linarith) (le_refl _))
    have hba : (c_cen - b_cen) - (b_cen + c_cen) / 24000 = (53 / 60 : ℝ) * D := by
      dsimp [b_cen, c_cen]; rw [hy_eq]; ring
    have hlog_cen : Real.log c_cen ≤ 4 * (Ln : ℝ) := by
      have h1 : Real.log c_cen ≤ Real.log (y + D) :=
        Real.log_le_log (by dsimp [c_cen]; linarith) (by dsimp [c_cen]; linarith)
      linarith
    have hm := mul_le_mul_of_nonneg_left hlog_cen (Nat.cast_nonneg P_cen.card)
    linarith
  obtain ⟨b_res, _, hA_fiber_card⟩ :=
    exists_odd_residue_fiber_ge P_cen h0 hh0_pos (fun p hp => (hP_cen_props p hp).2.1)
  let A := P_cen.filter (fun p => p % (2 * h0) = b_res)
  have hA_prime : ∀ p ∈ A, Nat.Prime p ∧ Odd p := by
    intro p hp
    have hp_cen := hP_cen_props p (Finset.mem_filter.mp hp).1
    exact ⟨hp_cen.1, hp_cen.2.1⟩
  have hA_int : ∀ p ∈ A, y - D / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ y + D / 2 := by
    intro p hp
    have hp_cen := hP_cen_props p (Finset.mem_filter.mp hp).1
    exact ⟨hp_cen.2.2.1.le, hp_cen.2.2.2⟩
  have hA_mod : ∀ p ∈ A, p % (2 * h0) = b_res :=
    fun p hp => (Finset.mem_filter.mp hp).2
  have hA_card : D < (C : ℝ) * ((2 * h0 : ℕ) : ℝ) * (A.card : ℝ) := by
    have h2_mul : 2 * P_cen.card ≤ (2 * h0) * A.card := by
      calc 2 * P_cen.card
          ≤ 2 * (h0 * A.card) := Nat.mul_le_mul_left 2 hA_fiber_card
        _ = (2 * h0) * A.card := (Nat.mul_assoc 2 h0 A.card).symm
    have h2_real : 2 * (P_cen.card : ℝ) ≤ ((2 * h0 : ℕ) : ℝ) * (A.card : ℝ) := by
      have hc : ((2 * P_cen.card : ℕ) : ℝ) ≤ (((2 * h0) * A.card : ℕ) : ℝ) :=
        Nat.cast_le.mpr h2_mul
      push_cast at hc ⊢
      exact hc
    have hm := mul_le_mul_of_nonneg_left h2_real (Nat.cast_nonneg C)
    dsimp [C] at hm ⊢
    push_cast at hm ⊢
    linarith [hP_cen_card_Ln]
  have hA_card_ge : 2 ≤ A.card := by
    have h2h0_le : ((2 * h0 : ℕ) : ℝ) ≤ 6 * (Ln : ℝ) := by
      have h6 : 2 * h0 ≤ 6 * Ln := by dsimp [H0] at hh0_le; omega
      exact_mod_cast h6
    have hLn_D : 36 * (Ln : ℝ) ^ 2 < D := by
      linarith [hLn2_le, hlog2_le, hn_lt_D]
    have hprod_le : (C : ℝ) * ((2 * h0 : ℕ) : ℝ) ≤ 18 * (Ln : ℝ) ^ 2 := by
      have hm := mul_le_mul_of_nonneg_left h2h0_le (Nat.cast_nonneg C)
      dsimp [C] at hm ⊢
      push_cast at hm ⊢
      linarith
    have hmul_A := mul_le_mul_of_nonneg_right hprod_le (Nat.cast_nonneg A.card)
    have hlt2 : 18 * (Ln : ℝ) ^ 2 * 2 < 18 * (Ln : ℝ) ^ 2 * (A.card : ℝ) := by
      linarith [hA_card, hLn_D, hmul_A]
    have hreal : (2 : ℝ) < (A.card : ℝ) :=
      lt_of_mul_lt_mul_left hlt2 (by positivity)
    exact (Nat.cast_lt.mp hreal).le
  have hD_upper : D < ((2 * C * (2 * h0) * 2 ^ k : ℕ) : ℝ) := by
    have hlog_lt : Real.log (y + D) < Real.log ((2 : ℝ) ^ k) := by
      rw [Real.log_pow]
      dsimp [k]
      push_cast
      have hlog2_lo : (693 / 1000 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hm := mul_lt_mul_of_pos_left hlog2_lo (by positivity : (0 : ℝ) < 6 * (Ln : ℝ))
      linarith [hlog_yD, hLn_ge, hlogn_gt]
    have hyD_lt_2k : y + D < (2 : ℝ) ^ k :=
      (Real.log_lt_log_iff (by linarith) (by positivity)).mp hlog_lt
    have h1_le : (1 : ℝ) ≤ ((2 * C * (2 * h0) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (by omega : 0 < 2 * C) (by omega : 0 < 2 * h0)
    have h2k_le : (2 : ℝ) ^ k ≤ ((2 * C * (2 * h0) * 2 ^ k : ℕ) : ℝ) := by
      have hm := mul_le_mul_of_nonneg_right h1_le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)
      push_cast at hm ⊢
      linarith
    linarith
  have hmod_supply : ∀ p : ℕ, Nat.Prime p → p ∣ h0 →
      ∃ u g : ℕ,
        (Nat.Prime u ∧ Odd u ∧ Nat.Prime (u + g) ∧ Odd (u + g) ∧
          y - D / 2 ≤ (u : ℝ) ∧ ((u + g : ℕ) : ℝ) ≤ y + D / 2 ∧ (g : ℝ) ≤ D / 2) ∧
        2 ∣ g ∧ ¬ (p ∣ g / 2) := by
    intro p hp_prime hp_dvd
    have hp_le_h0 : p ≤ h0 := Nat.le_of_dvd hh0_pos hp_dvd
    have hp_le_H0 : p ≤ H0 := hp_le_h0.trans hh0_le
    have hp_real : (p : ℝ) ≤ 3 * (Ln : ℝ) := by dsimp [H0] at hp_le_H0; exact_mod_cast hp_le_H0
    have hexp_cond : Real.exp ((2 / 5 : ℝ) * Real.log b_mid) ≤ (c_mid - b_mid) / (2 * (p : ℝ)) := by
      have hba : c_mid - b_mid = D / 2 := by dsimp [b_mid, c_mid]; ring
      rw [hba]
      apply exp_two_fifths_log_le_of_pow (by linarith) (by positivity)
      have hb_le_nX : b_mid ≤ (3 / 5 : ℝ) * ((n : ℝ) * X) := by
        have hy_hi : y ≤ (519 / 1000 : ℝ) * ((n : ℝ) * X) := by
          have hm := mul_le_mul_of_nonneg_left hm_hi.le hn_nonneg
          dsimp [y]; linarith
        dsimp [b_mid]; linarith [hD_pos]
      have hb2 : b_mid ^ 2 ≤ (9 / 25 : ℝ) * ((n : ℝ) * X) ^ 2 := by
        have hp2 := pow_le_pow_left₀ (by linarith) hb_le_nX 2
        linarith [show ((3 / 5 : ℝ) * ((n : ℝ) * X)) ^ 2 = (9 / 25 : ℝ) * ((n : ℝ) * X) ^ 2 by ring]
      have hLn3_le : (Ln : ℝ) ^ 3 ≤ (1 / 18 : ℝ) * (n : ℝ) := by
        have hp3 := pow_le_pow_left₀ (by positivity) hLn_ratio 3
        have hc : ((11 / 10 : ℝ) * Real.log (n : ℝ)) ^ 3 = (1331 / 1000 : ℝ) * (Real.log (n : ℝ)) ^ 3 := by ring
        linarith [hlogn3]
      have hLn6_le : (Ln : ℝ) ^ 6 ≤ (1 / 324 : ℝ) * (n : ℝ) ^ 2 := by
        have hp2 := pow_le_pow_left₀ (by positivity) hLn3_le 2
        linarith [show ((Ln : ℝ) ^ 3) ^ 2 = (Ln : ℝ) ^ 6 by ring,
                  show ((1 / 18 : ℝ) * (n : ℝ)) ^ 2 = (1 / 324 : ℝ) * (n : ℝ) ^ 2 by ring]
      have hLn5_le : (Ln : ℝ) ^ 5 ≤ (1 / 324 : ℝ) * (n : ℝ) ^ 3 := by
        have hLn1 : (1 : ℝ) ≤ (Ln : ℝ) := by exact_mod_cast (by omega : 1 ≤ Ln)
        have hm1 := mul_le_mul_of_nonneg_left hLn1 (by positivity : (0 : ℝ) ≤ (Ln : ℝ) ^ 5)
        have hn2_n3 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
          have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
          nlinarith [sq_nonneg (n : ℝ)]
        linarith [show (Ln : ℝ) ^ 5 * (Ln : ℝ) = (Ln : ℝ) ^ 6 by ring]
      have hD2_ge : ((n : ℝ) * X) / 7000 ≤ D / 2 := by linarith [hD_ge_nX]
      have h2p_pos : (0 : ℝ) < 2 * (p : ℝ) := by exact_mod_cast Nat.mul_pos (by decide) hp_prime.pos
      have h2p_le : 2 * (p : ℝ) ≤ 6 * (Ln : ℝ) := by linarith [hp_real]
      have hquot_ge : ((n : ℝ) * X) / (42000 * (Ln : ℝ)) ≤ (D / 2) / (2 * (p : ℝ)) := by
        have h1 : (D / 2) / (6 * (Ln : ℝ)) ≤ (D / 2) / (2 * (p : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) h2p_pos h2p_le
        have h2 : (((n : ℝ) * X) / 7000) / (6 * (Ln : ℝ)) ≤ (D / 2) / (6 * (Ln : ℝ)) :=
          div_le_div_of_nonneg_right hD2_ge (by positivity)
        have heq : (((n : ℝ) * X) / 7000) / (6 * (Ln : ℝ)) = ((n : ℝ) * X) / (42000 * (Ln : ℝ)) := by ring
        linarith
      have hquot5 : (((n : ℝ) * X) / (42000 * (Ln : ℝ))) ^ 5 ≤ ((D / 2) / (2 * (p : ℝ))) ^ 5 :=
        pow_le_pow_left₀ (by positivity) hquot_ge 5
      have hX3_ge : (283 * 10 ^ 8 : ℝ) ^ 3 ≤ X ^ 3 :=
        pow_le_pow_left₀ (by norm_num) hX_gt_283.le 3
      have hnX3_ge : (283 * 10 ^ 8 : ℝ) ^ 3 * (n : ℝ) ^ 3 ≤ ((n : ℝ) * X) ^ 3 := by
        have hm := mul_le_mul_of_nonneg_right hX3_ge (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 3)
        linarith [show X ^ 3 * (n : ℝ) ^ 3 = ((n : ℝ) * X) ^ 3 by ring]
      have hkey : (9 / 25 : ℝ) * (42000 * (Ln : ℝ)) ^ 5 ≤ ((n : ℝ) * X) ^ 3 := by
        have hc : (9 / 25 : ℝ) * (42000 * (Ln : ℝ)) ^ 5 =
            ((9 / 25 : ℝ) * 42000 ^ 5) * (Ln : ℝ) ^ 5 := by ring
        have hm := mul_le_mul_of_nonneg_left hLn5_le (by norm_num : (0 : ℝ) ≤ (9 / 25 : ℝ) * 42000 ^ 5)
        have hnum : ((9 / 25 : ℝ) * 42000 ^ 5) * (1 / 324 : ℝ) ≤ (283 * 10 ^ 8 : ℝ) ^ 3 := by norm_num
        have hm2 := mul_le_mul_of_nonneg_right hnum (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 3)
        linarith
      have hmul_key := mul_le_mul_of_nonneg_right hkey (by positivity : (0 : ℝ) ≤ ((n : ℝ) * X) ^ 2)
      have hden_pos : (0 : ℝ) < (42000 * (Ln : ℝ)) ^ 5 := by positivity
      have hmid5 : (9 / 25 : ℝ) * ((n : ℝ) * X) ^ 2 ≤ (((n : ℝ) * X) / (42000 * (Ln : ℝ))) ^ 5 := by
        rw [div_pow, le_div_iff₀ hden_pos]
        linarith [show ((n : ℝ) * X) ^ 3 * ((n : ℝ) * X) ^ 2 = ((n : ℝ) * X) ^ 5 by ring,
                  show (9 / 25 : ℝ) * ((n : ℝ) * X) ^ 2 * (42000 * (Ln : ℝ)) ^ 5 =
                    (9 / 25 : ℝ) * (42000 * (Ln : ℝ)) ^ 5 * ((n : ℝ) * X) ^ 2 by ring]
      exact hb2.trans (hmid5.trans hquot5)
    have hfilter_lt : ∀ c : ℕ, (P_mid.filter (fun x => x % (2 * p) = c)).card < P_mid.card := by
      intro c
      have hp_lt_b : (p : ℝ) < b_mid := by
        dsimp [b_mid]
        linarith [hp_real, hLn1_le, hlog2_le, hn_lt_D, hy_eq, hD_gt]
      have hexp_cond' : Real.exp ((2 / 5 : ℝ) * Real.log b_mid) ≤ (c_mid - b_mid) / (2 * p) := by
        simpa using hexp_cond
      have hup_div := apInterval_filter_mod_two_prime_sharp bmor imp hMV
        (b := b_mid) (c := c_mid) (p := p) (r := c) hp_prime
        (by linarith) (by dsimp [b_mid, c_mid]; linarith) hp_lt_b hexp_cond'
      have hup := (le_div_iff₀ (by linarith : 0 < Real.log b_mid)).mp hup_div
      have hba : (c_mid - b_mid) / 2 + (b_mid + c_mid) / 25000 = (181 / 500 : ℝ) * D := by
        dsimp [b_mid, c_mid]; rw [hy_eq]; ring
      rw [hba] at hup
      have hlow : (23 / 62 : ℝ) * D ≤ (P_mid.card : ℝ) * Real.log b_mid := by
        have hm := mul_le_mul_of_nonneg_left hlog_c_le_b (Nat.cast_nonneg P_mid.card)
        linarith [hP_mid_card_log]
      have hlt_log : ((P_mid.filter (fun x => x % (2 * p) = c)).card : ℝ) * Real.log b_mid <
          (P_mid.card : ℝ) * Real.log b_mid := by linarith
      have hlt_real : ((P_mid.filter (fun x => x % (2 * p) = c)).card : ℝ) < (P_mid.card : ℝ) :=
        lt_of_mul_lt_mul_right hlt_log (by linarith)
      exact_mod_cast hlt_real
    obtain ⟨u, hu_mem, v, hv_mem, hu_lt_v, hne_mod⟩ :=
      exists_incongruent_pair_of_card_filter_lt (fun x => x % (2 * p)) ⟨r0, hr0_mem⟩ hfilter_lt
    have hu_p := hP_mid_props u hu_mem
    have hv_p := hP_mid_props v hv_mem
    let g : ℕ := v - u
    have hug : u + g = v := by omega
    have hg_even : 2 ∣ g := by
      obtain ⟨m1, hm1⟩ := hu_p.2.1
      obtain ⟨m2, hm2⟩ := hv_p.2.1
      exact ⟨m2 - m1, by omega⟩
    have hndvd : ¬ (p ∣ g / 2) :=
      not_dvd_half_gap_of_mod_two_mul_ne hu_p.2.1 hv_p.2.1 hu_lt_v.le hne_mod
    have hg_le : (g : ℝ) ≤ D / 2 := by
      have hcast : (g : ℝ) = (v : ℝ) - (u : ℝ) := Nat.cast_sub hu_lt_v.le
      dsimp [b_mid, c_mid] at hu_p hv_p
      linarith [hu_p.2.2.1, hv_p.2.2.2]
    refine ⟨u, g, ⟨hu_p.1, hu_p.2.1, ?_, ?_, ?_, ?_, hg_le⟩, hg_even, hndvd⟩
    · rw [hug]; exact hv_p.1
    · rw [hug]; exact hv_p.2.1
    · dsimp [b_mid] at hu_p; linarith [hu_p.2.2.1]
    · rw [hug]; dsimp [c_mid] at hv_p; linarith [hv_p.2.2.2]
  exact t75_targets_from_evenIntervalGrid_supplies hn_pos hn_odd hC_ge hh0_pos hh0_le hsize_le
    y D rfl hD_pos hD_upper p_lo p_hi
    ⟨hplo_prime, hplo_odd, hplo_lo.le, hplo_hi⟩
    ⟨hphi_prime, hphi_odd, hphi_lo.le, hphi_hi⟩
    r0 ⟨hr0_props.1, hr0_props.2.1, by rw [hr1_eq]; exact hr1_props.1, by rw [hr1_eq]; exact hr1_props.2.1⟩
    ⟨by dsimp [b_mid] at hr0_props; linarith [hr0_props.2.2.1],
     by rw [hr1_eq]; dsimp [c_mid] at hr1_props; linarith [hr1_props.2.2.2]⟩
    A hA_prime hA_int hA_mod hA_card_ge hA_card hmod_supply

/-! ## Section 2: Unbounded Central-Band Completion (`ε = 15 / 10000`) -/

private theorem ut_central_completion_coeff_le {n : ℕ} (hn : 20 ≤ n) {ε X : ℝ}
    (hε : 0 < ε) (hX : 0 < X) :
    (1 + (7 + 1 / (n : ℝ)) * ε) * X + 2 * (ε * X) +
      (n : ℝ) * (6 * (ε * X) / ((n * n - 1 : ℕ) : ℝ)) ≤ (1 + 10 * ε) * X := by
  have hnR : (20 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < (n : ℝ) := by linarith
  have hηpos : 0 < ε * X := mul_pos hε hX
  have hn2_cast : ((n * n - 1 : ℕ) : ℝ) = (n : ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub (by nlinarith : 1 ≤ n * n)]
    push_cast; ring
  have hn2Pos : (0 : ℝ) < ((n * n - 1 : ℕ) : ℝ) := by rw [hn2_cast]; nlinarith
  have h1 : 1 / (n : ℝ) ≤ (1 / 20 : ℝ) := by
    rw [div_le_div_iff₀ hnPos (by norm_num)]
    linarith
  have h2 : (n : ℝ) * (6 * (ε * X) / ((n * n - 1 : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) * (ε * X) := by
    have hpoly : 12 * (n : ℝ) ≤ (n : ℝ) ^ 2 - 1 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hpoly hηpos.le
    rw [show (n : ℝ) * (6 * (ε * X) / ((n * n - 1 : ℕ) : ℝ)) =
      (6 * (n : ℝ) * (ε * X)) / ((n * n - 1 : ℕ) : ℝ) by ring]
    rw [div_le_iff₀ hn2Pos, hn2_cast]
    linarith
  have h3 : (1 / (n : ℝ)) * ε * X ≤ (1 / 20 : ℝ) * ε * X :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hε.le) hX.le
  linarith

private theorem ut_availableInterval_le_filter_unused {n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (lo hi : ℝ) (hleft : 1 ≤ lo) (hbc : lo ≤ hi) (hright : hi ≤ (poolMaximum n : ℝ)) :
    (availableInterval lo hi 2 1 (reserved.image (entry a))).card ≤
      ((actualUnusedPool a reserved).filter
        (fun v => lo < centralPoolValue v ∧ centralPoolValue v ≤ hi)).card := by
  let deleted := reserved.image (entry a)
  have hsub :
      availableInterval lo hi 2 1 deleted ⊆
        ((actualUnusedPool a reserved).filter
          (fun v => lo < centralPoolValue v ∧ centralPoolValue v ≤ hi)).image Subtype.val := by
    intro p hp
    have hm := Finset.mem_sdiff.mp hp
    have hp_pool := even_apInterval_subset_pool n lo hi 2 1
      (by linarith) (by linarith) hright (by decide) (by decide) p hm.1
    let v : pool n := ⟨p, hp_pool⟩
    have hv : v ∈ actualUnusedPool a reserved := by
      apply (mem_actualUnusedPool a reserved v).2
      intro z hz heq
      apply hm.2
      exact Finset.mem_image.mpr ⟨z, hz, heq.symm⟩
    have hint := (mem_apInterval_iff lo hi 2 1 (by linarith) (by linarith) p).mp hm.1
    refine Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, ?_⟩, rfl⟩
    exact ⟨hint.2.1, hint.2.2.1⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcard
  exact hcard

/-- Unbounded sharp central-band diagonal and off-diagonal completion for `n ≥ 35,735`
at `ε = 15 / 10000`, using Keepout `(0.355 * X, 0.578 * X]` avoidance and all-scale `thetaAP`
parity supply. -/
theorem ut_central_band_sharp_completion
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {L n : ℕ} (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (hn : 35735 ≤ n) (hodd : Odd n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols)
    (hload : 4 * (2 * (rows.length + cols.length) + 4) ≤ n)
    (a : Cell n ≃ Fin (n * n)) (full : Finset (Cell n))
    (hfull : full = packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols))
    (hreserve : 4 * full.card ≤ n * n)
    (hkeepout : ∀ v ∈ full.image (entry a), (v : ℝ) ≤ utKeepoutLo n ∨ utKeepoutHi n < (v : ℝ))
    (hμ₀_lo : (3566 / 10000 : ℝ) * utX n ≤ centralEntriesMean (actualUnusedPool a full) centralPoolValue)
    (hμ₀_hi : centralEntriesMean (actualUnusedPool a full) centralPoolValue ≤ (5764 / 10000 : ℝ) * utX n) :
    let ε : ℝ := 15 / 10000
    ∃ c : Cell n ≃ Fin (n * n),
      (∀ z ∈ full, entry c z = entry a z) ∧
      |(mainSum c : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry a z : ℝ)) +
        ((mainCells n \ full).card : ℝ) *
          centralEntriesMean (actualUnusedPool a full) centralPoolValue)| ≤
        2 * ε * utX n ∧
      |(antiSum c : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry a z : ℝ)) +
        ((antiCells n \ full).card : ℝ) *
          centralEntriesMean (actualUnusedPool a full) centralPoolValue)| ≤
        (201 / 100 : ℝ) * ε * utX n ∧
      (∀ i, |(rowSum c i : ℝ) - ((∑ z ∈ rowCells i ∩ full, (entry a z : ℝ)) +
        ((rowCells i \ full).card : ℝ) *
          centralEntriesMean (actualUnusedPool a full) centralPoolValue)| <
        (1 + 10 * ε) * utX n) ∧
      (∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ full, (entry a z : ℝ)) +
        ((columnCells i \ full).card : ℝ) *
          centralEntriesMean (actualUnusedPool a full) centralPoolValue)| <
        (1 + 10 * ε) * utX n) := by
  dsimp only
  let ε : ℝ := 15 / 10000
  let X : ℝ := utX n
  let μ₀ := centralEntriesMean (actualUnusedPool a full) centralPoolValue
  let η : ℝ := ε * X
  let δ : ℝ := 6 * η / ((n * n - 1 : ℕ) : ℝ)
  let final := full ∪ unreservedDiagonalCells full
  have hε_pos : 0 < ε := by dsimp [ε]; norm_num
  obtain ⟨_, hX_283, _, hlogX_gt, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  obtain ⟨_, _, _, _, _, hY_gt, _, _, _, _⟩ := ut_sharp_scale_bounds rs lower sharp upper hn
  have hX_pos : 0 < X := by dsimp [X, utX]; linarith
  have hlogX_pos : 0 < Real.log X := by dsimp [X, utX]; linarith
  have hη_pos : 0 < η := mul_pos hε_pos hX_pos
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hδ_nonneg : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ_le : δ ≤ (1 / 10000 : ℝ) * X := by
    have hn2_91 : 91 ≤ n * n := by nlinarith
    have hn2_90 : (90 : ℝ) ≤ ((n * n - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 90 ≤ n * n - 1 by omega)
    have hden_pos : (0 : ℝ) < ((n * n - 1 : ℕ) : ℝ) := by linarith
    dsimp [δ, η, ε]
    rw [div_le_iff₀ hden_pos]
    nlinarith
  have hkeep_lo : utKeepoutLo n ≤ μ₀ - η - δ := by
    dsimp [utKeepoutLo, X, η, ε] at hμ₀_lo hδ_le ⊢
    linarith
  have hkeep_hi : μ₀ + η + δ ≤ utKeepoutHi n := by
    dsimp [utKeepoutHi, X, η, ε] at hμ₀_hi hδ_le ⊢
    linarith
  have hkeep_1e9 : (10 ^ 9 : ℝ) ≤ utKeepoutLo n := by
    dsimp [utKeepoutLo, utX]; linarith
  have hkeep_le_X : utKeepoutHi n ≤ X := by
    dsimp [utKeepoutHi, X]; linarith
  -- Any subinterval of `(utKeepoutLo n, utKeepoutHi n]` has `0` intersection with `full.image (entry a)`
  have hzero_del : ∀ lo hi : ℝ, utKeepoutLo n ≤ lo → lo ≤ hi → hi ≤ utKeepoutHi n →
      apInterval lo hi 2 1 ∩ full.image (entry a) = ∅ := by
    intro lo hi hlo hbc hhi
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hpI, hpF⟩ := Finset.mem_inter.mp hp
    have hlo0 : 0 ≤ lo := by linarith
    have hm := (mem_apInterval_iff lo hi 2 1 hlo0 (hlo0.trans hbc) p).mp hpI
    rcases hkeepout p hpF with hL | hR
    · linarith [hm.2.1]
    · linarith [hm.2.2.1]
  -- Half-window stock helper on `(lo, hi] ⊆ (utKeepoutLo n, utKeepoutHi n]` of width `η / 2`
  have hhalf_stock : ∀ lo hi : ℝ, utKeepoutLo n ≤ lo → hi ≤ utKeepoutHi n → hi - lo = η / 2 →
      2 * n - 1 ≤ ((actualUnusedPool a full).filter
        (fun v => lo < centralPoolValue v ∧ centralPoolValue v ≤ hi)).card := by
    intro lo hi hlo hhi hlen
    have hbc : lo ≤ hi := by linarith
    have h1e9 : (10 ^ 9 : ℝ) ≤ lo := hkeep_1e9.trans hlo
    have hhiX : hi ≤ X := hhi.trans hkeep_le_X
    have hcard_div := apInterval_mod_two_card_lower_ge_1e9 bmor imp
      (b := lo) (c := hi) (X := X) h1e9 hbc hhiX
    have hnum : (59 / 100000 : ℝ) * X ≤ (hi - lo) - (lo + hi) / 7600 := by
      have hsum_ub : lo + hi ≤ 2 * utKeepoutHi n := by linarith
      dsimp [utKeepoutHi, X, η, ε] at hsum_ub hlen ⊢
      linarith
    have hY_eq : ((59 / 100000 : ℝ) * X) / Real.log X = (59 / 100000 : ℝ) * utY n := by
      dsimp [utY, X]; ring
    have hcard_lo : (59 / 100000 : ℝ) * utY n ≤ (apInterval lo hi 2 1).card := by
      rw [← hY_eq]
      exact (div_le_div_of_nonneg_right hnum hlogX_pos.le).trans hcard_div
    have h2n_lt : ((2 * n - 1 : ℕ) : ℝ) ≤ (59 / 100000 : ℝ) * utY n := by
      have hcast : ((2 * n - 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; linarith
      have hn2 : 35735 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      nlinarith [hY_gt]
    have hcard_2n : 2 * n - 1 ≤ (apInterval lo hi 2 1).card := by
      exact_mod_cast (h2n_lt.trans hcard_lo)
    have hemp := hzero_del lo hi hlo hbc hhi
    have havail_eq : availableInterval lo hi 2 1 (full.image (entry a)) = apInterval lo hi 2 1 := by
      dsimp [availableInterval]
      rw [Finset.sdiff_eq_self_iff_disjoint]
      exact Finset.disjoint_iff_inter_eq_empty.mpr hemp
    have hfilt := ut_availableInterval_le_filter_unused a full lo hi (by linarith) hbc
      (by simpa [X, utX] using hhiX)
    rw [havail_eq] at hfilt
    exact hcard_2n.trans hfilt
  have hcenter : centralCell n (by omega) ∉ full := by
    rw [hfull]
    exact fw_full_keepout_avoids_center hs (by omega) choice rows cols hrows hcols
  obtain ⟨hXcard, hYcard, hZcard, _, _, _, hXY, hXZ, _, hmainPart, hantiPart⟩ :=
    central_free_diagonal_geometry (by omega : 0 < n) hodd full hcenter
  have hdiagNeed : 1 + (centralFreeMain (by omega) full).card +
      (centralFreeAnti (by omega) full).card ≤ 2 * n - 1 := by omega
  have hlowStock : 1 + (centralFreeMain (by omega) full).card +
      (centralFreeAnti (by omega) full).card ≤
      ((actualUnusedPool a full).filter
        (fun v => μ₀ - η < centralPoolValue v ∧ centralPoolValue v ≤ μ₀ - η / 2)).card :=
    hdiagNeed.trans (hhalf_stock (μ₀ - η) (μ₀ - η / 2)
      (by linarith) (by linarith) (by ring))
  have hhighStock : 1 + (centralFreeMain (by omega) full).card +
      (centralFreeAnti (by omega) full).card ≤
      ((actualUnusedPool a full).filter
        (fun v => μ₀ + η / 2 < centralPoolValue v ∧ centralPoolValue v ≤ μ₀ + η)).card :=
    hdiagNeed.trans (hhalf_stock (μ₀ + η / 2) (μ₀ + η)
      (by linarith) (by linarith) (by ring))
  obtain ⟨b, _A, _B, _C, _, _, _, _, _, _, hfixed, hcentral, _, hcount, _, _, hshiftRaw,
      hmain, hanti, _, _⟩ :=
    central_place_odd_diagonals_exact_pool a full μ₀ η hη_pos (by omega) hodd hcenter hreserve
      (by dsimp only [μ₀]; rw [sub_self, abs_zero]; positivity) hlowStock hhighStock
  let μ₁ := centralEntriesMean (actualUnusedPool b final) centralPoolValue
  have hshift : |μ₁ - μ₀| ≤ δ :=
    hshiftRaw.trans (diagonal_mean_shift_uniform n (actualUnusedPool b final).card η
      (by omega) hη_pos.le hcount)
  have hshift_lo := (abs_le.mp hshift).1
  have hshift_hi := (abs_le.mp hshift).2
  have hμ₁_keep_lo : utKeepoutLo n ≤ μ₁ - η := by linarith
  have hμ₁_keep_hi : μ₁ + η ≤ utKeepoutHi n := by linarith
  have hdelPost := post_diagonal_deletions_from_widened_interval a b full μ₀ μ₁ η δ
    (by omega) hodd hfixed hη_pos.le hshift (by linarith)
  have hemp_wide : apInterval (μ₀ - η - δ) (μ₀ + η + δ) 2 1 ∩ full.image (entry a) = ∅ :=
    hzero_del (μ₀ - η - δ) (μ₀ + η + δ) hkeep_lo (by linarith) hkeep_hi
  have hdelPost' : (apInterval (μ₁ - η) (μ₁ + η) 2 1 ∩ final.image (entry b)).card ≤ 2 * n - 1 := by
    change (apInterval (μ₁ - η) (μ₁ + η) 2 1 ∩ final.image (entry b)).card ≤
      (apInterval (μ₀ - η - δ) (μ₀ + η + δ) 2 1 ∩ full.image (entry a)).card + (2 * n - 1) at hdelPost
    rw [hemp_wide, Finset.card_empty, zero_add] at hdelPost
    exact hdelPost
  have hfull_card_div := apInterval_mod_two_card_lower_ge_1e9 bmor imp
    (b := μ₁ - η) (c := μ₁ + η) (X := X) (hkeep_1e9.trans hμ₁_keep_lo) (by linarith)
    (hμ₁_keep_hi.trans hkeep_le_X)
  have hfull_num : (284 / 100000 : ℝ) * X ≤ ((μ₁ + η) - (μ₁ - η)) - ((μ₁ - η) + (μ₁ + η)) / 7600 := by
    have hsum_ub : (μ₁ - η) + (μ₁ + η) ≤ 2 * utKeepoutHi n := by linarith
    dsimp [utKeepoutHi, X, η, ε] at hsum_ub ⊢
    linarith
  have hfull_Y : (284 / 100000 : ℝ) * utY n ≤ (apInterval (μ₁ - η) (μ₁ + η) 2 1).card := by
    have hY_eq : ((284 / 100000 : ℝ) * X) / Real.log X = (284 / 100000 : ℝ) * utY n := by
      dsimp [utY, X]; ring
    rw [← hY_eq]
    exact (div_le_div_of_nonneg_right hfull_num hlogX_pos.le).trans hfull_card_div
  have h5n_le : ((3 * n + 1 + (2 * n - 1) : ℕ) : ℝ) ≤ (284 / 100000 : ℝ) * utY n := by
    have hcast : ((3 * n + 1 + (2 * n - 1) : ℕ) : ℝ) = 5 * (n : ℝ) := by
      have : 3 * n + 1 + (2 * n - 1) = 5 * n := by omega
      rw [this]; push_cast; ring
    have hn2 : 35735 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    rw [hcast]; nlinarith [hY_gt]
  have h5n_nat : (3 * n + 1) + (2 * n - 1) ≤ (apInterval (μ₁ - η) (μ₁ + η) 2 1).card := by
    exact_mod_cast (h5n_le.trans hfull_Y)
  have hsdiff_sum := Finset.card_sdiff_add_card_inter (apInterval (μ₁ - η) (μ₁ + η) 2 1) (final.image (entry b))
  have havail_3n1 : 3 * n + 1 ≤ (availableInterval (μ₁ - η) (μ₁ + η) 2 1 (final.image (entry b))).card := by
    dsimp [availableInterval]; omega
  have hstockN : 3 * n + 1 ≤ (centralExceptionStock b final η).card :=
    havail_3n1.trans (available_central_interval_le_stock b final η hη_pos.le
      (by linarith)
      (by simpa [μ₁, X, utX] using (hμ₁_keep_hi.trans hkeep_le_X)))
  have hstockN' : 3 * n + 1 ≤
      (centralExceptionStock b
        ((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
          LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪
          unreservedDiagonalCells (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
            LayerPacking.transposeCells (LayerPacking.layersSupport cols))) η).card := by
    simpa only [final, hfull] using hstockN
  obtain ⟨c, hfixedc', hrowsC', hcolsC', hmainc, hantic, _, _⟩ :=
    cy_full_keepout_sharp_central_completion hs hL (by omega) hodd choice rows cols
      hrows hcols hload b ε hε_pos.le hstockN'
  have hfixedc : ∀ z ∈ final, entry c z = entry b z := by
    simpa only [final, hfull] using hfixedc'
  have hrowsC : ∀ i, |(rowSum c i : ℝ) - ((∑ z ∈ rowCells i ∩ final, (entry b z : ℝ)) +
      ((rowCells i \ final).card : ℝ) * μ₁)| < (1 + (7 + 1 / (n : ℝ)) * ε) * X := by
    simpa only [final, μ₁, X, utX, hfull] using hrowsC'
  have hcolsC : ∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ final, (entry b z : ℝ)) +
      ((columnCells i \ final).card : ℝ) * μ₁)| < (1 + (7 + 1 / (n : ℝ)) * ε) * X := by
    simpa only [final, μ₁, X, utX, hfull] using hcolsC'
  have htrans := diagonal_preassignment_rows_columns_transfer a b c full μ₀ μ₁ η δ
    ((1 + (7 + 1 / (n : ℝ)) * ε) * X) hη_pos.le hδ_nonneg hfixed hcentral hshift hrowsC hcolsC
  have hcoeff : (1 + (7 + 1 / (n : ℝ)) * ε) * X + 2 * η + (n : ℝ) * δ ≤ (1 + 10 * ε) * X :=
    ut_central_completion_coeff_le (by omega) hε_pos hX_pos
  have hmainCard : 1 + (centralFreeMain (by omega) full).card = (mainCells n \ full).card := by
    rw [← hmainPart, Finset.card_union_of_disjoint hXY, hXcard]
  have hantiCard : 1 + (centralFreeAnti (by omega) full).card = (antiCells n \ full).card := by
    rw [← hantiPart, Finset.card_union_of_disjoint hXZ, hXcard]
  refine ⟨c, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hfixedc z (Finset.mem_union_left _ hz)).trans (hfixed z hz)
  · rw [hmainc, ← hmainCard]
    simpa only [η, X, mul_assoc] using hmain
  · rw [hantic, ← hantiCard]
    simpa only [η, X, mul_assoc] using hanti
  · intro i
    exact (htrans.1 i).trans_le hcoeff
  · intro i
    exact (htrans.2 i).trans_le hcoeff

/-! ## Section 3: Physical Installation, Growth Balancing, Routing, & Diagonal Repair -/

private theorem ut_layersSupport_eq_image {n : ℕ} (layers : List (LayerPacking.Layer n)) :
    LayerPacking.layersSupport layers = Finset.univ.image (LayerPacking.sequenceCell layers) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun hz => LayerPacking.sequenceCell_covers layers z hz,
    fun ⟨x, hx⟩ => hx ▸ LayerPacking.layerSupport_subset (layers.get x.1) layers
      (List.get_mem layers x.1) (LayerPacking.sequenceCell_mem layers x.1 x.2)⟩

private theorem ut_transposeCells_layersSupport_eq_image {n : ℕ} (layers : List (LayerPacking.Layer n)) :
    LayerPacking.transposeCells (LayerPacking.layersSupport layers) =
      Finset.univ.image (fun x => (LayerPacking.sequenceCell layers x).swap) := by
  rw [LayerPacking.transposeCells, ut_layersSupport_eq_image, Finset.image_image]
  rfl

private theorem ut_packedLayers_support_cards {n : ℕ} {res₁ res₂ : Finset (Cell n)}
    {rows cols : List (LayerPacking.Layer n)}
    (hr : LayerPacking.PackedLayers res₁ rows)
    (hc : LayerPacking.PackedLayers res₂ cols) :
    (LayerPacking.layersSupport rows).card = 2 * n * rows.length ∧
    (LayerPacking.transposeCells (LayerPacking.layersSupport cols)).card = 2 * n * cols.length := by
  have hc_inj : Function.Injective (fun x => (LayerPacking.sequenceCell cols x).swap) :=
    Prod.swap_injective.comp hc.sequenceCell_injective
  rw [ut_layersSupport_eq_image rows, ut_transposeCells_layersSupport_eq_image cols,
    Finset.card_image_of_injective _ hr.sequenceCell_injective,
    Finset.card_image_of_injective _ hc_inj]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  exact ⟨by ring, by ring⟩

private theorem ut_mean_dist_le_pairwise_width {n : ℕ} (hn : 0 < n) (g : Fin n → ℝ) (y W : ℝ)
    (hsum : (∑ i : Fin n, g i) = (n : ℝ) * y)
    (hw : ∀ i j : Fin n, |g i - g j| ≤ W) (i : Fin n) :
    |g i - y| ≤ W := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hid : (n : ℝ) * (g i - y) = ∑ j : Fin n, (g i - g j) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hsum]
    ring
  have habs : (n : ℝ) * |g i - y| ≤ (n : ℝ) * W := by
    calc (n : ℝ) * |g i - y|
        = |(n : ℝ) * (g i - y)| := by rw [abs_mul, abs_of_pos hn_pos]
      _ = |∑ j : Fin n, (g i - g j)| := by rw [hid]
      _ ≤ ∑ j : Fin n, |g i - g j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, W := Finset.sum_le_sum (fun j _ => hw i j)
      _ = (n : ℝ) * W := by simp [nsmul_eq_mul]
  exact le_of_mul_le_mul_left habs hn_pos

private theorem ut_packedLabelSupport_univ_subset {L n : ℕ}
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) :
    packedLabelSupport hs choice Finset.univ ⊆ packedRectangleSupport hs choice := by
  intro z hz
  obtain ⟨i, _, hmem⟩ := Finset.mem_biUnion.mp hz
  rw [mem_rectangleCells] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨(i, 0), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨(i, 1), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨(i, 2), Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨(i, 3), Finset.mem_univ _, rfl⟩

private theorem ut_mainSum_and_antiSum_le_n_mul_poolMaximum {n : ℕ} (b : Cell n ≃ Fin (n * n)) :
    (mainSum b : ℝ) ≤ (n : ℝ) * (poolMaximum n : ℝ) ∧
    (antiSum b : ℝ) ≤ (n : ℝ) * (poolMaximum n : ℝ) := by
  have hentry : ∀ z : Cell n, entry b z ≤ poolMaximum n :=
    fun z => pool_le_poolMaximum ⟨b z, rfl⟩
  have hm : mainSum b ≤ n * poolMaximum n := by
    calc mainSum b = ∑ i : Fin n, entry b (i, i) := rfl
      _ ≤ ∑ _i : Fin n, poolMaximum n := Finset.sum_le_sum (fun i _ => hentry (i, i))
      _ = n * poolMaximum n := by simp
  have ha : antiSum b ≤ n * poolMaximum n := by
    calc antiSum b = ∑ i : Fin n, entry b (i, i.rev) := rfl
      _ ≤ ∑ _i : Fin n, poolMaximum n := Finset.sum_le_sum (fun i _ => hentry (i, i.rev))
      _ = n * poolMaximum n := by simp
  exact ⟨by exact_mod_cast hm, by exact_mod_cast ha⟩

private theorem ut_rowSum_and_columnSum_total {n : ℕ} (b : Cell n ≃ Fin (n * n)) :
    (∑ r : Fin n, rowSum b r) = Lucas.poolTotal n ∧
    (∑ col : Fin n, columnSum b col) = Lucas.poolTotal n := by
  have hr : (∑ r : Fin n, rowSum b r) = Lucas.poolTotal n := by
    change (∑ r : Fin n, ∑ c : Fin n, entry b (r, c)) = Lucas.poolTotal n
    exact (Fintype.sum_prod_type (entry b)).symm.trans (Lucas.placement_total n b)
  have hc : (∑ col : Fin n, columnSum b col) = Lucas.poolTotal n := by
    change (∑ col : Fin n, ∑ r : Fin n, entry b (r, col)) = Lucas.poolTotal n
    rw [Finset.sum_comm]
    exact hr
  exact ⟨hr, hc⟩

/-- Evaluate the rectangle + `(2 - q) * μ₀` term on row `r` inside `[0, 2 * utX n]`. -/
private theorem ut_row_rect_term_bounds {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (a : Cell n ≃ Fin (n * n))
    {μ₀ : ℝ} (hμ_nn : 0 ≤ μ₀) (hμ_hi : μ₀ ≤ utX n) (r : Fin n) :
    let reserved := packedRectangleSupport hs choice
    let q := (rowCells r ∩ reserved).card
    q ≤ 2 ∧
    0 ≤ (∑ z ∈ rowCells r ∩ reserved, (entry a z : ℝ)) + ((2 - q : ℕ) : ℝ) * μ₀ ∧
    (∑ z ∈ rowCells r ∩ reserved, (entry a z : ℝ)) + ((2 - q : ℕ) : ℝ) * μ₀ ≤ 2 * utX n := by
  let reserved := packedRectangleSupport hs choice
  have hset : rowCells r ∩ reserved = (LayerPacking.rowUsed reserved r).image (fun j => (r, j)) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_inter, mem_rowCells, LayerPacking.rowUsed, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
    exact ⟨fun ⟨hi, hres⟩ => ⟨j, by subst hi; exact hres, hi.symm, rfl⟩,
      fun ⟨j', hres, hi, hj⟩ => by subst hi hj; exact ⟨rfl, hres⟩⟩
  have hq : (rowCells r ∩ reserved).card ≤ 2 := by
    rw [hset, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
    exact packedRectangleSupport_row_load hs choice r
  have hsum_le : (∑ z ∈ rowCells r ∩ reserved, (entry a z : ℝ)) ≤
      ((rowCells r ∩ reserved).card : ℝ) * utX n := by
    calc (∑ z ∈ rowCells r ∩ reserved, (entry a z : ℝ))
        ≤ ∑ _z ∈ rowCells r ∩ reserved, utX n := by
          apply Finset.sum_le_sum; intro z _
          have hle : entry a z ≤ poolMaximum n := pool_le_poolMaximum ⟨a z, rfl⟩
          dsimp [utX]; exact_mod_cast hle
      _ = ((rowCells r ∩ reserved).card : ℝ) * utX n := by simp [nsmul_eq_mul]
  have hrem_le : ((2 - (rowCells r ∩ reserved).card : ℕ) : ℝ) * μ₀ ≤
      ((2 - (rowCells r ∩ reserved).card : ℕ) : ℝ) * utX n :=
    mul_le_mul_of_nonneg_left hμ_hi (Nat.cast_nonneg _)
  have h2_eq : ((rowCells r ∩ reserved).card : ℝ) + ((2 - (rowCells r ∩ reserved).card : ℕ) : ℝ) = 2 := by
    rw [Nat.cast_sub hq]; push_cast; ring
  refine ⟨hq, ?_, ?_⟩
  · exact add_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hμ_nn)
  · linarith [show ((rowCells r ∩ reserved).card : ℝ) * utX n +
        ((2 - (rowCells r ∩ reserved).card : ℕ) : ℝ) * utX n = 2 * utX n by
      rw [← add_mul, h2_eq]]

/-- Symmetric evaluation of the rectangle + `(2 - q) * μ₀` term on column `col` inside `[0, 2 * utX n]`. -/
private theorem ut_col_rect_term_bounds {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (a : Cell n ≃ Fin (n * n))
    {μ₀ : ℝ} (hμ_nn : 0 ≤ μ₀) (hμ_hi : μ₀ ≤ utX n) (col : Fin n) :
    let reserved := packedRectangleSupport hs choice
    let q := (columnCells col ∩ reserved).card
    q ≤ 2 ∧
    0 ≤ (∑ z ∈ columnCells col ∩ reserved, (entry a z : ℝ)) + ((2 - q : ℕ) : ℝ) * μ₀ ∧
    (∑ z ∈ columnCells col ∩ reserved, (entry a z : ℝ)) + ((2 - q : ℕ) : ℝ) * μ₀ ≤ 2 * utX n := by
  let reserved := packedRectangleSupport hs choice
  have hset : columnCells col ∩ reserved = (LayerPacking.colUsed reserved col).image (fun i => (i, col)) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_inter, mem_columnCells, LayerPacking.colUsed, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
    exact ⟨fun ⟨hj, hres⟩ => ⟨i, by subst hj; exact hres, rfl, hj.symm⟩,
      fun ⟨i', hres, hi, hj⟩ => by subst hi hj; exact ⟨rfl, hres⟩⟩
  have hq : (columnCells col ∩ reserved).card ≤ 2 := by
    rw [hset, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
    exact packedRectangleSupport_column_load hs choice col
  have hsum_le : (∑ z ∈ columnCells col ∩ reserved, (entry a z : ℝ)) ≤
      ((columnCells col ∩ reserved).card : ℝ) * utX n := by
    calc (∑ z ∈ columnCells col ∩ reserved, (entry a z : ℝ))
        ≤ ∑ _z ∈ columnCells col ∩ reserved, utX n := by
          apply Finset.sum_le_sum; intro z _
          have hle : entry a z ≤ poolMaximum n := pool_le_poolMaximum ⟨a z, rfl⟩
          dsimp [utX]; exact_mod_cast hle
      _ = ((columnCells col ∩ reserved).card : ℝ) * utX n := by simp [nsmul_eq_mul]
  have hrem_le : ((2 - (columnCells col ∩ reserved).card : ℕ) : ℝ) * μ₀ ≤
      ((2 - (columnCells col ∩ reserved).card : ℕ) : ℝ) * utX n :=
    mul_le_mul_of_nonneg_left hμ_hi (Nat.cast_nonneg _)
  have h2_eq : ((columnCells col ∩ reserved).card : ℝ) + ((2 - (columnCells col ∩ reserved).card : ℕ) : ℝ) = 2 := by
    rw [Nat.cast_sub hq]; push_cast; ring
  refine ⟨hq, ?_, ?_⟩
  · exact add_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hμ_nn)
  · linarith [show ((columnCells col ∩ reserved).card : ℝ) * utX n +
        ((2 - (columnCells col ∩ reserved).card : ℕ) : ℝ) * utX n = 2 * utX n by
      rw [← add_mul, h2_eq]]

/-- Exact ordinary row-sum + `(1 / 2)` row-gap divergence midpoint identity on row `r`. -/
private theorem ut_row_ord_midpoint_eq {S n : ℕ} {res₁ res₂ : Finset (Cell n)}
    (p : Fin 3 → Equiv.Perm (Fin n))
    (rows cols : List (LayerPacking.Layer n))
    (hrS : rows.length = S * 3) (hcS : cols.length = S * 3)
    (hrmap : rows.map Prod.fst = bridgeRepeatedPermutations S p)
    (hr : LayerPacking.PackedLayers res₁ rows)
    (hc : LayerPacking.PackedLayers res₂ cols)
    (a : Cell n ≃ Fin (n * n))
    (ordFn : Fin S → UTEdge n → Bool → ℕ)
    (ordGap : Fin S → UTEdge n → ℕ)
    (hrow_gap : ∀ s l e, ordFn s (false, (l, e)) true = ordFn s (false, (l, e)) false + ordGap s (false, (l, e)))
    (hrow_a : ∀ x : Fin rows.length × (Fin n × Bool),
      let sl := finProdFinEquiv.symm (Fin.cast hrS x.1)
      entry a (LayerPacking.sequenceCell rows x) = ordFn sl.1 (false, (sl.2, x.2.1)) x.2.2)
    (hcol_a : ∀ x : Fin cols.length × (Fin n × Bool),
      let sl := finProdFinEquiv.symm (Fin.cast hcS x.1)
      entry a (LayerPacking.sequenceCell cols x).swap = ordFn sl.1 (true, (sl.2, x.2.1)) x.2.2)
    (sumGapR : Fin 3 × Fin n → ℕ)
    (hsumGapR : ∀ e : Fin 3 × Fin n, sumGapR e = ∑ s : Fin S, ordGap s (false, e))
    (r : Fin n) :
    (∑ z ∈ rowCells r ∩ LayerPacking.layersSupport rows, (entry a z : ℝ)) +
    (∑ z ∈ rowCells r ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols), (entry a z : ℝ)) +
    (1 / 2 : ℝ) * (∑ e : Fin 3 × Fin n,
      (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (sumGapR e : ℤ)) e r : ℝ)) =
    ∑ s : Fin S, ∑ l : Fin 3,
      (let gc := (cols.get (bridgeStageLayerIndex hcS s l)).2
       (((ordFn s (false, (l, r)) false + ordFn s (false, (l, r)) true : ℕ) : ℝ) / 2 +
        ((ordFn s (false, (l, (p l).symm r)) false + ordFn s (false, (l, (p l).symm r)) true : ℕ) : ℝ) / 2 +
        ((ordFn s (true, (l, gc.symm r)) false + ordFn s (true, (l, gc.symm r)) true : ℕ) : ℝ))) := by
  have hfilter_inter : ∀ (T : Finset (Cell n)),
      (∑ z ∈ rowCells r ∩ T, (entry a z : ℝ)) = ∑ z ∈ T, (if z.1 = r then (entry a z : ℝ) else 0) := by
    intro T
    have heq : rowCells r ∩ T = T.filter (fun z => z.1 = r) := by ext z; simp [and_comm]
    rw [heq, Finset.sum_filter]
  have hrow_sum : (∑ z ∈ rowCells r ∩ LayerPacking.layersSupport rows, (entry a z : ℝ)) =
      ∑ s : Fin S, ∑ l : Fin 3,
        ((ordFn s (false, (l, r)) false : ℝ) + (ordFn s (false, (l, (p l).symm r)) true : ℝ)) := by
    rw [hfilter_inter, ut_layersSupport_eq_image rows,
      Finset.sum_image (fun x _ y _ h => hr.sequenceCell_injective h),
      Fintype.sum_prod_type]
    let eR : Fin S × Fin 3 ≃ Fin rows.length := finProdFinEquiv.trans (finCongr hrS.symm)
    rw [← Equiv.sum_comp eR, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro l _
    have heR_eq : eR (s, l) = bridgeStageLayerIndex hrS s l := rfl
    rw [heR_eq, Fintype.sum_prod_type]
    have hsl_eq : finProdFinEquiv.symm (Fin.cast hrS (bridgeStageLayerIndex hrS s l)) = (s, l) := by
      have hc_eq : Fin.cast hrS (bridgeStageLayerIndex hrS s l) = finProdFinEquiv (s, l) := by
        ext; simp [bridgeStageLayerIndex]
      rw [hc_eq, Equiv.symm_apply_apply]
    have hπ_eq : ∀ e : Fin n, (rows.get (bridgeStageLayerIndex hrS s l)).1 e = p l e :=
      fun e => bridgeStageLayer_endpoints rows hrS p hrmap s l e
    have hinner : ∀ e : Fin n,
        (∑ b : Bool, (if (LayerPacking.sequenceCell rows (bridgeStageLayerIndex hrS s l, (e, b))).1 = r then
            (entry a (LayerPacking.sequenceCell rows (bridgeStageLayerIndex hrS s l, (e, b))) : ℝ) else 0)) =
        (if e = r then (ordFn s (false, (l, e)) false : ℝ) else 0) +
        (if p l e = r then (ordFn s (false, (l, e)) true : ℝ) else 0) := by
      intro e
      rw [Fintype.sum_bool]
      have haT := hrow_a (bridgeStageLayerIndex hrS s l, (e, true))
      have haF := hrow_a (bridgeStageLayerIndex hrS s l, (e, false))
      dsimp only at haT haF
      rw [hsl_eq] at haT haF
      rw [haT, haF]
      have h1 : (LayerPacking.sequenceCell rows (bridgeStageLayerIndex hrS s l, (e, true))).1 = p l e := hπ_eq e
      have h2 : (LayerPacking.sequenceCell rows (bridgeStageLayerIndex hrS s l, (e, false))).1 = e := rfl
      rw [h1, h2, add_comm]
    simp only [hinner, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    congr 1
    rw [← Equiv.sum_comp (p l).symm]
    simp only [Equiv.apply_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hcol_sum : (∑ z ∈ rowCells r ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols), (entry a z : ℝ)) =
      ∑ s : Fin S, ∑ l : Fin 3,
        (let gc := (cols.get (bridgeStageLayerIndex hcS s l)).2
         ((ordFn s (true, (l, gc.symm r)) false : ℝ) + (ordFn s (true, (l, gc.symm r)) true : ℝ))) := by
    have hc_inj : Function.Injective (fun x => (LayerPacking.sequenceCell cols x).swap) :=
      Prod.swap_injective.comp hc.sequenceCell_injective
    rw [hfilter_inter, ut_transposeCells_layersSupport_eq_image cols,
      Finset.sum_image (fun x _ y _ h => hc_inj h), Fintype.sum_prod_type]
    let eC : Fin S × Fin 3 ≃ Fin cols.length := finProdFinEquiv.trans (finCongr hcS.symm)
    rw [← Equiv.sum_comp eC, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro l _
    have heC_eq : eC (s, l) = bridgeStageLayerIndex hcS s l := rfl
    rw [heC_eq, Fintype.sum_prod_type]
    have hsl_eq : finProdFinEquiv.symm (Fin.cast hcS (bridgeStageLayerIndex hcS s l)) = (s, l) := by
      have hc_eq : Fin.cast hcS (bridgeStageLayerIndex hcS s l) = finProdFinEquiv (s, l) := by
        ext; simp [bridgeStageLayerIndex]
      rw [hc_eq, Equiv.symm_apply_apply]
    set gc := (cols.get (bridgeStageLayerIndex hcS s l)).2
    have hinner : ∀ e : Fin n,
        (∑ b : Bool, (if ((LayerPacking.sequenceCell cols (bridgeStageLayerIndex hcS s l, (e, b))).swap).1 = r then
            (entry a (LayerPacking.sequenceCell cols (bridgeStageLayerIndex hcS s l, (e, b))).swap : ℝ) else 0)) =
        (if gc e = r then
          (ordFn s (true, (l, e)) false : ℝ) + (ordFn s (true, (l, e)) true : ℝ) else 0) := by
      intro e
      rw [Fintype.sum_bool]
      have haT := hcol_a (bridgeStageLayerIndex hcS s l, (e, true))
      have haF := hcol_a (bridgeStageLayerIndex hcS s l, (e, false))
      dsimp only at haT haF
      rw [hsl_eq] at haT haF
      rw [haT, haF]
      have h1 : ((LayerPacking.sequenceCell cols (bridgeStageLayerIndex hcS s l, (e, true))).swap).1 = gc e := rfl
      have h2 : ((LayerPacking.sequenceCell cols (bridgeStageLayerIndex hcS s l, (e, false))).swap).1 = gc e := rfl
      rw [h1, h2]
      split_ifs <;> ring
    simp only [hinner]
    rw [← Equiv.sum_comp gc.symm]
    simp only [Equiv.apply_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hdiv_sum : (∑ e : Fin 3 × Fin n,
      (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (sumGapR e : ℤ)) e r : ℝ)) =
      ∑ s : Fin S, ∑ l : Fin 3,
        ((ordGap s (false, (l, r)) : ℝ) - (ordGap s (false, (l, (p l).symm r)) : ℝ)) := by
    rw [Fintype.sum_prod_type]
    have hper_l : ∀ l : Fin 3,
        (∑ e : Fin n, (edgeTransfer Prod.snd (fun x : Fin 3 × Fin n => p x.1 x.2)
          (fun x => (sumGapR x : ℤ)) (l, e) r : ℝ)) =
        (sumGapR (l, r) : ℝ) - (sumGapR (l, (p l).symm r) : ℝ) := by
      intro l
      have hcast_et : ∀ e : Fin n,
          (edgeTransfer Prod.snd (fun x : Fin 3 × Fin n => p x.1 x.2)
            (fun x => (sumGapR x : ℤ)) (l, e) r : ℝ) =
          (if e = r then (sumGapR (l, e) : ℝ) else 0) -
          (if p l e = r then (sumGapR (l, e) : ℝ) else 0) := by
        intro e; unfold edgeTransfer; dsimp only; split_ifs <;> push_cast <;> ring
      simp only [hcast_et, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      congr 1
      rw [← Equiv.sum_comp (p l).symm]
      simp only [Equiv.apply_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hrad_eq : ∀ (l : Fin 3) (e : Fin n),
        (sumGapR (l, e) : ℝ) = ∑ s : Fin S, (ordGap s (false, (l, e)) : ℝ) := by
      intro l e; rw [hsumGapR (l, e)]; push_cast; rfl
    simp only [hper_l, hrad_eq, ← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
  rw [hrow_sum, hcol_sum, hdiv_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro l _
  have hg1 : (ordFn s (false, (l, r)) true : ℝ) =
      (ordFn s (false, (l, r)) false : ℝ) + (ordGap s (false, (l, r)) : ℝ) := by
    exact_mod_cast hrow_gap s l r
  have hg2 : (ordFn s (false, (l, (p l).symm r)) true : ℝ) =
      (ordFn s (false, (l, (p l).symm r)) false : ℝ) + (ordGap s (false, (l, (p l).symm r)) : ℝ) := by
    exact_mod_cast hrow_gap s l ((p l).symm r)
  dsimp only
  push_cast
  linarith

/-- Symmetric column-sum + `(1 / 2)` column-gap divergence midpoint identity on column `col`. -/
private theorem ut_col_ord_midpoint_eq {S n : ℕ} {res₁ res₂ : Finset (Cell n)}
    (p : Fin 3 → Equiv.Perm (Fin n))
    (rows cols : List (LayerPacking.Layer n))
    (hrS : rows.length = S * 3) (hcS : cols.length = S * 3)
    (hcmap : cols.map Prod.fst = bridgeRepeatedPermutations S p)
    (hr : LayerPacking.PackedLayers res₁ rows)
    (hc : LayerPacking.PackedLayers res₂ cols)
    (a : Cell n ≃ Fin (n * n))
    (ordFn : Fin S → UTEdge n → Bool → ℕ)
    (ordGap : Fin S → UTEdge n → ℕ)
    (hcol_gap : ∀ s l e, ordFn s (true, (l, e)) true = ordFn s (true, (l, e)) false + ordGap s (true, (l, e)))
    (hrow_a : ∀ x : Fin rows.length × (Fin n × Bool),
      let sl := finProdFinEquiv.symm (Fin.cast hrS x.1)
      entry a (LayerPacking.sequenceCell rows x) = ordFn sl.1 (false, (sl.2, x.2.1)) x.2.2)
    (hcol_a : ∀ x : Fin cols.length × (Fin n × Bool),
      let sl := finProdFinEquiv.symm (Fin.cast hcS x.1)
      entry a (LayerPacking.sequenceCell cols x).swap = ordFn sl.1 (true, (sl.2, x.2.1)) x.2.2)
    (sumGapC : Fin 3 × Fin n → ℕ)
    (hsumGapC : ∀ e : Fin 3 × Fin n, sumGapC e = ∑ s : Fin S, ordGap s (true, e))
    (col : Fin n) :
    (∑ z ∈ columnCells col ∩ LayerPacking.layersSupport rows, (entry a z : ℝ)) +
    (∑ z ∈ columnCells col ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols), (entry a z : ℝ)) +
    (1 / 2 : ℝ) * (∑ e : Fin 3 × Fin n,
      (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (sumGapC e : ℤ)) e col : ℝ)) =
    ∑ s : Fin S, ∑ l : Fin 3,
      (let gr := (rows.get (bridgeStageLayerIndex hrS s l)).2
       (((ordFn s (false, (l, gr.symm col)) false + ordFn s (false, (l, gr.symm col)) true : ℕ) : ℝ) +
        ((ordFn s (true, (l, col)) false + ordFn s (true, (l, col)) true : ℕ) : ℝ) / 2 +
        ((ordFn s (true, (l, (p l).symm col)) false + ordFn s (true, (l, (p l).symm col)) true : ℕ) : ℝ) / 2)) := by
  have hfilter_inter : ∀ (T : Finset (Cell n)),
      (∑ z ∈ columnCells col ∩ T, (entry a z : ℝ)) = ∑ z ∈ T, (if z.2 = col then (entry a z : ℝ) else 0) := by
    intro T
    have heq : columnCells col ∩ T = T.filter (fun z => z.2 = col) := by ext z; simp [and_comm]
    rw [heq, Finset.sum_filter]
  have hrow_sum : (∑ z ∈ columnCells col ∩ LayerPacking.layersSupport rows, (entry a z : ℝ)) =
      ∑ s : Fin S, ∑ l : Fin 3,
        (let gr := (rows.get (bridgeStageLayerIndex hrS s l)).2
         ((ordFn s (false, (l, gr.symm col)) false : ℝ) + (ordFn s (false, (l, gr.symm col)) true : ℝ))) := by
    rw [hfilter_inter, ut_layersSupport_eq_image rows,
      Finset.sum_image (fun x _ y _ h => hr.sequenceCell_injective h),
      Fintype.sum_prod_type]
    let eR : Fin S × Fin 3 ≃ Fin rows.length := finProdFinEquiv.trans (finCongr hrS.symm)
    rw [← Equiv.sum_comp eR, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro l _
    have heR_eq : eR (s, l) = bridgeStageLayerIndex hrS s l := rfl
    rw [heR_eq, Fintype.sum_prod_type]
    have hsl_eq : finProdFinEquiv.symm (Fin.cast hrS (bridgeStageLayerIndex hrS s l)) = (s, l) := by
      have hc_eq : Fin.cast hrS (bridgeStageLayerIndex hrS s l) = finProdFinEquiv (s, l) := by
        ext; simp [bridgeStageLayerIndex]
      rw [hc_eq, Equiv.symm_apply_apply]
    set gr := (rows.get (bridgeStageLayerIndex hrS s l)).2
    have hinner : ∀ e : Fin n,
        (∑ b : Bool, (if (LayerPacking.sequenceCell rows (bridgeStageLayerIndex hrS s l, (e, b))).2 = col then
            (entry a (LayerPacking.sequenceCell rows (bridgeStageLayerIndex hrS s l, (e, b))) : ℝ) else 0)) =
        (if gr e = col then
          (ordFn s (false, (l, e)) false : ℝ) + (ordFn s (false, (l, e)) true : ℝ) else 0) := by
      intro e
      rw [Fintype.sum_bool]
      have haT := hrow_a (bridgeStageLayerIndex hrS s l, (e, true))
      have haF := hrow_a (bridgeStageLayerIndex hrS s l, (e, false))
      dsimp only at haT haF
      rw [hsl_eq] at haT haF
      rw [haT, haF]
      have h1 : (LayerPacking.sequenceCell rows (bridgeStageLayerIndex hrS s l, (e, true))).2 = gr e := rfl
      have h2 : (LayerPacking.sequenceCell rows (bridgeStageLayerIndex hrS s l, (e, false))).2 = gr e := rfl
      rw [h1, h2]
      split_ifs <;> ring
    simp only [hinner]
    rw [← Equiv.sum_comp gr.symm]
    simp only [Equiv.apply_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hcol_sum : (∑ z ∈ columnCells col ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols), (entry a z : ℝ)) =
      ∑ s : Fin S, ∑ l : Fin 3,
        ((ordFn s (true, (l, col)) false : ℝ) + (ordFn s (true, (l, (p l).symm col)) true : ℝ)) := by
    have hc_inj : Function.Injective (fun x => (LayerPacking.sequenceCell cols x).swap) :=
      Prod.swap_injective.comp hc.sequenceCell_injective
    rw [hfilter_inter, ut_transposeCells_layersSupport_eq_image cols,
      Finset.sum_image (fun x _ y _ h => hc_inj h), Fintype.sum_prod_type]
    let eC : Fin S × Fin 3 ≃ Fin cols.length := finProdFinEquiv.trans (finCongr hcS.symm)
    rw [← Equiv.sum_comp eC, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro l _
    have heC_eq : eC (s, l) = bridgeStageLayerIndex hcS s l := rfl
    rw [heC_eq, Fintype.sum_prod_type]
    have hsl_eq : finProdFinEquiv.symm (Fin.cast hcS (bridgeStageLayerIndex hcS s l)) = (s, l) := by
      have hc_eq : Fin.cast hcS (bridgeStageLayerIndex hcS s l) = finProdFinEquiv (s, l) := by
        ext; simp [bridgeStageLayerIndex]
      rw [hc_eq, Equiv.symm_apply_apply]
    have hπ_eq : ∀ e : Fin n, (cols.get (bridgeStageLayerIndex hcS s l)).1 e = p l e :=
      fun e => bridgeStageLayer_endpoints cols hcS p hcmap s l e
    have hinner : ∀ e : Fin n,
        (∑ b : Bool, (if ((LayerPacking.sequenceCell cols (bridgeStageLayerIndex hcS s l, (e, b))).swap).2 = col then
            (entry a (LayerPacking.sequenceCell cols (bridgeStageLayerIndex hcS s l, (e, b))).swap : ℝ) else 0)) =
        (if e = col then (ordFn s (true, (l, e)) false : ℝ) else 0) +
        (if p l e = col then (ordFn s (true, (l, e)) true : ℝ) else 0) := by
      intro e
      rw [Fintype.sum_bool]
      have haT := hcol_a (bridgeStageLayerIndex hcS s l, (e, true))
      have haF := hcol_a (bridgeStageLayerIndex hcS s l, (e, false))
      dsimp only at haT haF
      rw [hsl_eq] at haT haF
      rw [haT, haF]
      have h1 : ((LayerPacking.sequenceCell cols (bridgeStageLayerIndex hcS s l, (e, true))).swap).2 = p l e := hπ_eq e
      have h2 : ((LayerPacking.sequenceCell cols (bridgeStageLayerIndex hcS s l, (e, false))).swap).2 = e := rfl
      rw [h1, h2, add_comm]
    simp only [hinner, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    congr 1
    rw [← Equiv.sum_comp (p l).symm]
    simp only [Equiv.apply_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hdiv_sum : (∑ e : Fin 3 × Fin n,
      (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (sumGapC e : ℤ)) e col : ℝ)) =
      ∑ s : Fin S, ∑ l : Fin 3,
        ((ordGap s (true, (l, col)) : ℝ) - (ordGap s (true, (l, (p l).symm col)) : ℝ)) := by
    rw [Fintype.sum_prod_type]
    have hper_l : ∀ l : Fin 3,
        (∑ e : Fin n, (edgeTransfer Prod.snd (fun x : Fin 3 × Fin n => p x.1 x.2)
          (fun x => (sumGapC x : ℤ)) (l, e) col : ℝ)) =
        (sumGapC (l, col) : ℝ) - (sumGapC (l, (p l).symm col) : ℝ) := by
      intro l
      have hcast_et : ∀ e : Fin n,
          (edgeTransfer Prod.snd (fun x : Fin 3 × Fin n => p x.1 x.2)
            (fun x => (sumGapC x : ℤ)) (l, e) col : ℝ) =
          (if e = col then (sumGapC (l, e) : ℝ) else 0) -
          (if p l e = col then (sumGapC (l, e) : ℝ) else 0) := by
        intro e; unfold edgeTransfer; dsimp only; split_ifs <;> push_cast <;> ring
      simp only [hcast_et, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      congr 1
      rw [← Equiv.sum_comp (p l).symm]
      simp only [Equiv.apply_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hrad_eq : ∀ (l : Fin 3) (e : Fin n),
        (sumGapC (l, e) : ℝ) = ∑ s : Fin S, (ordGap s (true, (l, e)) : ℝ) := by
      intro l e; rw [hsumGapC (l, e)]; push_cast; rfl
    simp only [hper_l, hrad_eq, ← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
  rw [hrow_sum, hcol_sum, hdiv_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro l _
  have hg1 : (ordFn s (true, (l, col)) true : ℝ) =
      (ordFn s (true, (l, col)) false : ℝ) + (ordGap s (true, (l, col)) : ℝ) := by
    exact_mod_cast hcol_gap s l col
  have hg2 : (ordFn s (true, (l, (p l).symm col)) true : ℝ) =
      (ordFn s (true, (l, (p l).symm col)) false : ℝ) + (ordGap s (true, (l, (p l).symm col)) : ℝ) := by
    exact_mod_cast hcol_gap s l ((p l).symm col)
  dsimp only
  push_cast
  linarith

/-- Extract fiberwise `Equiv.Perm` on `β` from a stage-preserving self-equivalence of `α × β`. -/
private def ut_fiber_perm_of_stage_equiv {α β : Type*}
    (e0 : (α × β) ≃ (α × β)) (he0 : ∀ x : α × β, (e0 x).1 = x.1) (g : α) : Equiv.Perm β where
  toFun u := (e0 (g, u)).2
  invFun v := (e0.symm (g, v)).2
  left_inv u := by
    dsimp only
    have hpair : (g, (e0 (g, u)).2) = e0 (g, u) := Prod.ext (he0 (g, u)).symm rfl
    rw [hpair, Equiv.symm_apply_apply]
  right_inv v := by
    dsimp only
    have hsymm : (e0.symm (g, v)).1 = g := by
      have h := he0 (e0.symm (g, v))
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    have hpair : (g, (e0.symm (g, v)).2) = e0.symm (g, v) := Prod.ext hsymm.symm rfl
    rw [hpair, Equiv.apply_symm_apply]

private theorem ut_activeRectangleSupport_univ {L n : ℕ}
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) :
    activeRectangleSupport hs choice Finset.univ = packedRectangleSupport hs choice := by
  unfold activeRectangleSupport packedRectangleSupport
  rw [Finset.univ_product_univ]

/-- Equivalence between packed row/column sequence indices and `(Fin S × UTEdge n × Bool)`. -/
private def utOrdIdxEquiv {n S rlen clen : ℕ} (hrS : rlen = S * 3) (hcS : clen = S * 3) :
    ((Fin rlen × (Fin n × Bool)) ⊕ (Fin clen × (Fin n × Bool))) ≃
      (Fin S × UTEdge n × Bool) where
  toFun
    | Sum.inl ⟨i, e, b⟩ =>
      let sl := finProdFinEquiv.symm (Fin.cast hrS i)
      (sl.1, (false, (sl.2, e)), b)
    | Sum.inr ⟨i, e, b⟩ =>
      let sl := finProdFinEquiv.symm (Fin.cast hcS i)
      (sl.1, (true, (sl.2, e)), b)
  invFun
    | (s, (false, (l, e)), b) => Sum.inl (Fin.cast hrS.symm (finProdFinEquiv (s, l)), (e, b))
    | (s, (true, (l, e)), b) => Sum.inr (Fin.cast hcS.symm (finProdFinEquiv (s, l)), (e, b))
  left_inv x := by
    rcases x with ⟨i, e, b⟩ | ⟨i, e, b⟩
    · dsimp only
      rw [Equiv.apply_symm_apply]
      exact congrArg (fun j => Sum.inl (j, (e, b))) (Fin.ext rfl)
    · dsimp only
      rw [Equiv.apply_symm_apply]
      exact congrArg (fun j => Sum.inr (j, (e, b))) (Fin.ext rfl)
  right_inv y := by
    rcases y with ⟨s, ⟨br, l, e⟩, b⟩
    cases br
    · dsimp only
      have hc : Fin.cast hrS (Fin.cast hrS.symm (finProdFinEquiv (s, l))) = finProdFinEquiv (s, l) :=
        Fin.ext rfl
      rw [hc, Equiv.symm_apply_apply]
    · dsimp only
      have hc : Fin.cast hcS (Fin.cast hcS.symm (finProdFinEquiv (s, l))) = finProdFinEquiv (s, l) :=
        Fin.ext rfl
      rw [hc, Equiv.symm_apply_apply]

/-- Complete upper-tail proof of `Sude.HasSquare n` for every odd `n ≥ 35,735` from the
published analytic premises. -/
theorem upper_tail_hasSquare
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports) (hMV : MVBrunTitchmarsh)
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp)
    (upper : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) (hn_odd : Odd n) :
    HasSquare n := by
  classical
  have hn_pos : 0 < n := by omega
  let X : ℝ := utX n
  obtain ⟨_, hX_283, _, _, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  obtain ⟨_, _, hLn_ge11, _, _, _, _, hclog, _, _⟩ := ut_sharp_scale_bounds rs lower sharp upper hn
  have hLn11_lin := ut_ln_le_linear_11 rs lower sharp upper hn
  have hX_pos : 0 < X := by dsimp [X, utX]; linarith
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- Scalar relationships between `utH0Max`, `utWOrd`, `utWDiag`, and `n`
  have hWOrd_ge_95 : (95 : ℝ) ≤ (utWOrd n : ℝ) := by
    exact_mod_cast (show 95 ≤ utWOrd n by dsimp [utWOrd]; omega)
  have hWOrd_lin_lo : (1 / 430 : ℝ) * (n : ℝ) + 11 ≤ (utWOrd n : ℝ) := by
    have hd : n - 429 ≤ 430 * (n / 430) := by omega
    have hnat : n + 4730 ≤ 430 * utWOrd n := by dsimp [utWOrd]; omega
    have hreal : (n : ℝ) + 4730 ≤ 430 * (utWOrd n : ℝ) := by exact_mod_cast hnat
    linarith
  have hn_le_WOrd : (n : ℝ) ≤ 430 * (utWOrd n : ℝ) := by linarith
  have hH0Max_le_WOrd : (utH0Max n : ℝ) ≤ (utWOrd n : ℝ) := by
    have hH : (utH0Max n : ℝ) = 3 * (utLn n : ℝ) + 15 := by dsimp [utH0Max]; push_cast; ring
    linarith [hLn11_lin, hWOrd_lin_lo, hnR]
  have hWDiag_lin_lo : (1 / 2000 : ℝ) * (n : ℝ) ≤ (utWDiag n : ℝ) := by
    have hnat : n ≤ 2000 * utWDiag n := by dsimp [utWDiag]; omega
    have hreal : (n : ℝ) ≤ 2000 * (utWDiag n : ℝ) := by exact_mod_cast hnat
    linarith
  have hH0Max_le_5WDiag : (utH0Max n : ℝ) ≤ 5 * (utWDiag n : ℝ) := by
    have hnat : utH0Max n ≤ 5 * utWDiag n := by dsimp [utH0Max, utWDiag]; omega
    exact_mod_cast hnat
  -- Step 1: Obtain `UTRoleWitness` and place diagonal rectangles (`a₀` -> `a₁`)
  obtain ⟨rw⟩ := ut_role_witness bmor imp hMV rs lower sharp upper hn
  let rectVal : Fin rw.L × Fin 4 → pool n :=
    fun x => ⟨(rw.diagRect x.1).corners x.2, rw.hV_sub _ (rw.hdiag_mem x.1 x.2)⟩
  have hrect_inj : Function.Injective rectVal :=
    fun x y h => rw.hdiag_inj (congrArg Subtype.val h)
  let a₀ : Cell n ≃ Fin (n * n) := Fintype.equivOfCardEq (by simp [Cell])
  obtain ⟨a₁, hrect_a₁, _⟩ :=
    place_distinct_pool_entries_preserving a₀ (packedRectangleCorner rw.hs rw.choice) rectVal ∅
      (packedRectangleCorner_injective rw.hs rw.choice) hrect_inj (by simp) (by simp)
  let reserved := packedRectangleSupport rw.hs rw.choice
  -- Step 2: Obtain expander `p` and pack physical layers `rows` and `cols`
  obtain ⟨p, hderange, hexp⟩ := fc2k_permutation_expander_exists (by omega : 2001 ≤ n)
  let perms := bridgeRepeatedPermutations rw.S p
  have hlen_p : perms.length = rw.S * 3 := bridgeRepeatedPermutations_length p
  have hder : ∀ π ∈ perms, ∀ v, π v ≠ v := bridgeRepeatedPermutations_derange p hderange
  let rv_raw (x : Fin perms.length × (Fin n × Bool)) : pool n :=
    let sl := finProdFinEquiv.symm (Fin.cast hlen_p x.1)
    ⟨rw.ordRaw sl.1 (false, (sl.2, x.2.1)) x.2.2, rw.hV_sub _ (rw.hord_mem sl.1 (false, (sl.2, x.2.1)) x.2.2)⟩
  let cv_raw (x : Fin perms.length × (Fin n × Bool)) : pool n :=
    let sl := finProdFinEquiv.symm (Fin.cast hlen_p x.1)
    ⟨rw.ordRaw sl.1 (true, (sl.2, x.2.1)) x.2.2, rw.hV_sub _ (rw.hord_mem sl.1 (true, (sl.2, x.2.1)) x.2.2)⟩
  let rg_raw (i : Fin perms.length) (e : Fin n) : ℕ :=
    let sl := finProdFinEquiv.symm (Fin.cast hlen_p i)
    rw.ordGap sl.1 (false, (sl.2, e))
  let cg_raw (i : Fin perms.length) (e : Fin n) : ℕ :=
    let sl := finProdFinEquiv.symm (Fin.cast hlen_p i)
    rw.ordGap sl.1 (true, (sl.2, e))
  have hrinj_raw : Function.Injective rv_raw := by
    intro x y h
    let slx := finProdFinEquiv.symm (Fin.cast hlen_p x.1)
    let sly := finProdFinEquiv.symm (Fin.cast hlen_p y.1)
    have hinj := @UTRoleWitness.hord_inj _ rw
      (slx.1, (false, (slx.2, x.2.1)), x.2.2) (sly.1, (false, (sly.2, y.2.1)), y.2.2)
      (congrArg Subtype.val h)
    rcases Prod.mk.inj hinj with ⟨hs_eq, hrest⟩
    rcases Prod.mk.inj hrest with ⟨hu_eq, hb_eq⟩
    rcases Prod.mk.inj (Prod.mk.inj hu_eq).2 with ⟨hl_eq, he_eq⟩
    have hsl : slx = sly := Prod.ext hs_eq hl_eq
    exact Prod.ext (Fin.cast_injective hlen_p (finProdFinEquiv.symm.injective hsl)) (Prod.ext he_eq hb_eq)
  have hcinj_raw : Function.Injective cv_raw := by
    intro x y h
    let slx := finProdFinEquiv.symm (Fin.cast hlen_p x.1)
    let sly := finProdFinEquiv.symm (Fin.cast hlen_p y.1)
    have hinj := @UTRoleWitness.hord_inj _ rw
      (slx.1, (true, (slx.2, x.2.1)), x.2.2) (sly.1, (true, (sly.2, y.2.1)), y.2.2)
      (congrArg Subtype.val h)
    rcases Prod.mk.inj hinj with ⟨hs_eq, hrest⟩
    rcases Prod.mk.inj hrest with ⟨hu_eq, hb_eq⟩
    rcases Prod.mk.inj (Prod.mk.inj hu_eq).2 with ⟨hl_eq, he_eq⟩
    have hsl : slx = sly := Prod.ext hs_eq hl_eq
    exact Prod.ext (Fin.cast_injective hlen_p (finProdFinEquiv.symm.injective hsl)) (Prod.ext he_eq hb_eq)
  have hsep_raw : ∀ x y, (rv_raw x).val ≠ (cv_raw y).val := by
    intro x y heq
    let slx := finProdFinEquiv.symm (Fin.cast hlen_p x.1)
    let sly := finProdFinEquiv.symm (Fin.cast hlen_p y.1)
    have hinj := @UTRoleWitness.hord_inj _ rw
      (slx.1, (false, (slx.2, x.2.1)), x.2.2) (sly.1, (true, (sly.2, y.2.1)), y.2.2) heq
    exact Bool.noConfusion (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hinj).2).1).1
  have hravoid_raw : ∀ x z, z ∈ reserved → (rv_raw x).val ≠ entry a₁ z := by
    intro x z hz heq
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
    rw [hrect_a₁ y] at heq
    let slx := finProdFinEquiv.symm (Fin.cast hlen_p x.1)
    exact rw.hdiag_ord_disj y (slx.1, (false, (slx.2, x.2.1)), x.2.2) heq.symm
  have hcavoid_raw : ∀ x z, z ∈ reserved → (cv_raw x).val ≠ entry a₁ z := by
    intro x z hz heq
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
    rw [hrect_a₁ y] at heq
    let slx := finProdFinEquiv.symm (Fin.cast hlen_p x.1)
    exact rw.hdiag_ord_disj y (slx.1, (true, (slx.2, x.2.1)), x.2.2) heq.symm
  have hrgap_raw : ∀ i e, (rv_raw (i, (e, true))).val = (rv_raw (i, (e, false))).val + rg_raw i e :=
    fun i e => (rw.hord_pair _ _).1
  have hcgap_raw : ∀ i e, (cv_raw (i, (e, true))).val = (cv_raw (i, (e, false))).val + cg_raw i e :=
    fun i e => (rw.hord_pair _ _).1
  have hcap_ord : 4 * (2 + 2 * perms.length + 2 * perms.length) + 8 < n := by
    rw [hlen_p]; have := rw.hpack_ord; omega
  obtain ⟨rows, cols, hrlen, hclen, _a_raw, hrmap, hcmap, hr, hc, hdis_rc,
      hrowsafe, hcolsafe, _, _, _, _, _, hrow_layer_cards, hcol_layer_cards, _, _⟩ :=
    LayerPacking.pack_and_install_two_networks perms perms reserved hder hder
      (packedRectangleSupport_row_load rw.hs rw.choice) (packedRectangleSupport_column_load rw.hs rw.choice)
      hcap_ord a₁ rv_raw cv_raw hrinj_raw hcinj_raw hsep_raw hravoid_raw hcavoid_raw
      rg_raw cg_raw hrgap_raw hcgap_raw
  have hrS : rows.length = rw.S * 3 := hrlen.trans hlen_p
  have hcS : cols.length = rw.S * 3 := hclen.trans hlen_p
  -- Step 3: Simultaneous Growth midpoint balancing across all `2 * n` rows and columns
  let gStage (g : Fin rw.G) : Fin rw.S := ⟨g.val, lt_of_lt_of_le g.isLt rw.hGS⟩
  let gr (s : Fin rw.S) (l : Fin 3) : Equiv.Perm (Fin n) := (rows.get (bridgeStageLayerIndex hrS s l)).2
  let gc (s : Fin rw.S) (l : Fin 3) : Equiv.Perm (Fin n) := (cols.get (bridgeStageLayerIndex hcS s l)).2
  let slotsG : Finset (Fin rw.G × UTEdge n) := Finset.univ
  let linesG : Finset (Fin n ⊕ Fin n) := Finset.univ
  let xVal : Fin rw.G × UTEdge n → ℝ := fun gu =>
    (((rw.ordRaw (gStage gu.1) gu.2 false + rw.ordRaw (gStage gu.1) gu.2 true : ℕ) : ℝ)) / 2
  let wLine : Fin n ⊕ Fin n → Fin rw.G × UTEdge n → ℝ := fun line gu =>
    match line, gu.2 with
    | Sum.inl r, (false, (l, e)) => (if e = r then (1 : ℝ) else 0) + (if p l e = r then (1 : ℝ) else 0)
    | Sum.inl r, (true, (l, e)) => if gc (gStage gu.1) l e = r then (2 : ℝ) else 0
    | Sum.inr col, (false, (l, e)) => if gr (gStage gu.1) l e = col then (2 : ℝ) else 0
    | Sum.inr col, (true, (l, e)) => (if e = col then (1 : ℝ) else 0) + (if p l e = col then (1 : ℝ) else 0)
  have hslots_filter_card : ∀ g : Fin rw.G, (slotsG.filter (fun s => s.1 = g)).card = 6 * n := by
    intro g
    have hf_eq : slotsG.filter (fun s => s.1 = g) = (Finset.univ : Finset (UTEdge n)).image (fun u => (g, u)) := by
      ext ⟨g', u⟩; simp [slotsG, eq_comm]
    rw [hf_eq, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h),
      Finset.card_univ, Fintype.card_congr (utEdgeEquiv n), Fintype.card_fin]
  have hw_nn : ∀ line ∈ linesG, ∀ s ∈ slotsG, 0 ≤ wLine line s := by
    intro line _ ⟨g, b, l, e⟩ _
    cases line <;> cases b <;> dsimp [wLine] <;> positivity
  have hw_tot4 : ∀ s ∈ slotsG, (∑ line ∈ linesG, wLine line s) ≤ 4 := by
    rintro ⟨g, b, l, e⟩ _
    dsimp [linesG]
    rw [Fintype.sum_sum_type]
    cases b <;> dsimp [wLine] <;>
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    · have h2 : (∑ col : Fin n, if gr (gStage g) l e = col then (2 : ℝ) else 0) = 2 := by
        simp [Finset.sum_ite_eq]
      linarith
    · have h1 : (∑ r : Fin n, if gc (gStage g) l e = r then (2 : ℝ) else 0) = 2 := by
        simp [Finset.sum_ite_eq]
      linarith
  have hx_width : ∀ u ∈ slotsG, ∀ v ∈ slotsG, u.1 = v.1 → xVal v - xVal u ≤ utMidWidth n := by
    rintro ⟨g₁, u₁⟩ _ ⟨g₂, u₂⟩ _ hgg
    dsimp only at hgg; subst hgg
    have hsp := rw.hgrowth_mid_spread g₁ u₁ u₂
    have hpair1 : (((rw.ordRaw (gStage g₁) u₁ false + rw.ordRaw (gStage g₁) u₁ true : ℕ) : ℝ)) / 2 =
        (rw.ordRaw (gStage g₁) u₁ false : ℝ) + (rw.ordGap (gStage g₁) u₁ : ℝ) / 2 := by
      rw [(rw.hord_pair (gStage g₁) u₁).1]; push_cast; ring
    have hpair2 : (((rw.ordRaw (gStage g₁) u₂ false + rw.ordRaw (gStage g₁) u₂ true : ℕ) : ℝ)) / 2 =
        (rw.ordRaw (gStage g₁) u₂ false : ℝ) + (rw.ordGap (gStage g₁) u₂ : ℝ) / 2 := by
      rw [(rw.hord_pair (gStage g₁) u₂).1]; push_cast; ring
    dsimp [xVal]; rw [hpair1, hpair2]; exact hsp
  obtain ⟨e_assign, he_stage, he_bal⟩ :=
    prefix_deterministic_stage_assignment_four slotsG slotsG linesG Prod.fst Prod.fst
      xVal wLine (utMidWidth n) (6 * n)
      (by dsimp [utMidWidth]; positivity)
      (fun _ => rfl) (fun g => (hslots_filter_card g).le) hw_nn hw_tot4 hx_width
  let e_univ : {s // s ∈ slotsG} ≃ (Fin rw.G × UTEdge n) := Equiv.subtypeUnivEquiv Finset.mem_univ
  let e0 : (Fin rw.G × UTEdge n) ≃ (Fin rw.G × UTEdge n) :=
    e_univ.symm.trans (e_assign.trans e_univ)
  have he0 : ∀ x : Fin rw.G × UTEdge n, (e0 x).1 = x.1 := fun x => he_stage ⟨x, Finset.mem_univ x⟩
  let permG : Fin rw.G → Equiv.Perm (UTEdge n) := ut_fiber_perm_of_stage_equiv e0 he0
  have he0_eq : ∀ (g : Fin rw.G) (u : UTEdge n), e0 (g, u) = (g, permG g u) :=
    fun g u => Prod.ext (he0 (g, u)) rfl
  -- Step 4: Re-install `rw.ordPerm permG` onto `rows` and `cols` in a single call (`a₁` -> `a`)
  let ordCells : (Fin rows.length × (Fin n × Bool)) ⊕ (Fin cols.length × (Fin n × Bool)) → Cell n :=
    Sum.elim (LayerPacking.sequenceCell rows) (fun x => (LayerPacking.sequenceCell cols x).swap)
  let ordIdxEquiv := utOrdIdxEquiv (n := n) hrS hcS
  let ordVals : (Fin rows.length × (Fin n × Bool)) ⊕ (Fin cols.length × (Fin n × Bool)) → pool n :=
    fun t =>
      let y := ordIdxEquiv t
      ⟨rw.ordPerm permG y.1 y.2.1 y.2.2, rw.hV_sub _ (rw.ordPerm_mem permG y.1 y.2.1 y.2.2)⟩
  have hordCells_inj : Function.Injective ordCells := by
    have hc_inj : Function.Injective (fun x => (LayerPacking.sequenceCell cols x).swap) :=
      Prod.swap_injective.comp hc.sequenceCell_injective
    rintro (x | x) (y | y) heq
    · exact congrArg Sum.inl (hr.sequenceCell_injective heq)
    · exfalso
      dsimp only [ordCells, Sum.elim_inl, Sum.elim_inr] at heq
      have hm1 : LayerPacking.sequenceCell rows x ∈ LayerPacking.layersSupport rows := by
        rw [ut_layersSupport_eq_image]; exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
      have hm2 : (LayerPacking.sequenceCell cols y).swap ∈
          LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
        rw [ut_transposeCells_layersSupport_eq_image]; exact Finset.mem_image_of_mem _ (Finset.mem_univ y)
      exact Finset.disjoint_left.mp hdis_rc hm1 (heq ▸ hm2)
    · exfalso
      dsimp only [ordCells, Sum.elim_inl, Sum.elim_inr] at heq
      have hm1 : LayerPacking.sequenceCell rows y ∈ LayerPacking.layersSupport rows := by
        rw [ut_layersSupport_eq_image]; exact Finset.mem_image_of_mem _ (Finset.mem_univ y)
      have hm2 : (LayerPacking.sequenceCell cols x).swap ∈
          LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
        rw [ut_transposeCells_layersSupport_eq_image]; exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
      exact Finset.disjoint_left.mp hdis_rc hm1 (heq.symm ▸ hm2)
    · exact congrArg Sum.inr (hc_inj heq)
  have hordVals_inj : Function.Injective ordVals :=
    fun t₁ t₂ h => ordIdxEquiv.injective (@UTRoleWitness.ordPerm_inj _ rw permG
      (ordIdxEquiv t₁) (ordIdxEquiv t₂) (congrArg Subtype.val h))
  have hordCells_new : ∀ t, ordCells t ∉ reserved := by
    rintro (x | x)
    · have hm : LayerPacking.sequenceCell rows x ∈ LayerPacking.layersSupport rows := by
        rw [ut_layersSupport_eq_image]; exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
      exact (hrowsafe _ hm).1
    · have hm : (LayerPacking.sequenceCell cols x).swap ∈
          LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
        rw [ut_transposeCells_layersSupport_eq_image]; exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
      exact (hcolsafe _ hm).1
  have hordVals_avoid : ∀ t z, z ∈ reserved → (ordVals t).val ≠ entry a₁ z := by
    intro t z hz heq
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    rw [hrect_a₁ x] at heq
    exact rw.diag_ordPerm_disj permG x (ordIdxEquiv t) heq.symm
  obtain ⟨a, hord_a, hfixed_res_a⟩ :=
    place_distinct_pool_entries_preserving a₁ ordCells ordVals reserved
      hordCells_inj hordVals_inj hordCells_new hordVals_avoid
  have hrect_a : ∀ x : Fin rw.L × Fin 4, entry a (packedRectangleCorner rw.hs rw.choice x) =
      (rw.diagRect x.1).corners x.2 := by
    intro x
    rw [hfixed_res_a _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩), hrect_a₁ x]
  have hrow_a : ∀ x : Fin rows.length × (Fin n × Bool),
      let sl := finProdFinEquiv.symm (Fin.cast hrS x.1)
      entry a (LayerPacking.sequenceCell rows x) = rw.ordPerm permG sl.1 (false, (sl.2, x.2.1)) x.2.2 :=
    fun x => hord_a (Sum.inl x)
  have hcol_a : ∀ x : Fin cols.length × (Fin n × Bool),
      let sl := finProdFinEquiv.symm (Fin.cast hcS x.1)
      entry a (LayerPacking.sequenceCell cols x).swap = rw.ordPerm permG sl.1 (true, (sl.2, x.2.1)) x.2.2 :=
    fun x => hord_a (Sum.inr x)
  -- Step 5: `full` support, `full.image (entry a) = rw.V_res`, `μ₀` enclosure, & central completion (`a` -> `c`)
  let full := reserved ∪ LayerPacking.layersSupport rows ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport cols)
  have hdis_res_r : Disjoint reserved (LayerPacking.layersSupport rows) := hr.reserved_disjoint
  have hdis_res_c : Disjoint (reserved ∪ LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
    apply Finset.disjoint_left.mpr; intro z hz12 hzc
    rcases Finset.mem_union.mp hz12 with hzr | hzl
    · exact (hcolsafe z hzc).1 hzr
    · exact Finset.disjoint_left.mp hdis_rc hzl hzc
  have hres_card : reserved.card = 4 * rw.L := by
    dsimp [reserved, packedRectangleSupport]
    rw [Finset.card_image_of_injective _ (packedRectangleCorner_injective rw.hs rw.choice)]
    simp [mul_comm]
  obtain ⟨hr_card, hc_card⟩ := ut_packedLayers_support_cards hr hc
  have hfull_card : full.card = 4 * rw.L + 12 * n * rw.S := by
    dsimp [full]
    rw [Finset.card_union_of_disjoint hdis_res_c, Finset.card_union_of_disjoint hdis_res_r,
      hres_card, hr_card, hc_card, hrS, hcS]
    ring
  have hres_le : 4 * full.card ≤ n * n := by
    rw [hfull_card]; have := rw.hres_quarter; omega
  have hfull_image : full.image (entry a) = rw.V_res := by
    dsimp [full]
    have him_res : reserved.image (entry a) =
        Finset.univ.image (fun x : Fin rw.L × Fin 4 => (rw.diagRect x.1).corners x.2) := by
      dsimp [reserved, packedRectangleSupport]
      rw [Finset.image_image]
      apply Finset.image_congr; intro x _; exact hrect_a x
    have him_ord : (LayerPacking.layersSupport rows ∪
          LayerPacking.transposeCells (LayerPacking.layersSupport cols)).image (entry a) =
        Finset.univ.image (fun y : Fin rw.S × UTEdge n × Bool => rw.ordPerm permG y.1 y.2.1 y.2.2) := by
      rw [Finset.image_union, ut_layersSupport_eq_image rows, ut_transposeCells_layersSupport_eq_image cols,
        Finset.image_image, Finset.image_image]
      ext v
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
      constructor
      · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
        · rw [hrow_a x]; exact ⟨ordIdxEquiv (Sum.inl x), rfl⟩
        · rw [hcol_a x]; exact ⟨ordIdxEquiv (Sum.inr x), rfl⟩
      · rintro ⟨y, rfl⟩
        rcases hsum : ordIdxEquiv.symm y with x | x
        · left; refine ⟨x, ?_⟩
          have hy : ordIdxEquiv (Sum.inl x) = y := by rw [← hsum, Equiv.apply_symm_apply]
          rw [hrow_a x, ← hy]; rfl
        · right; refine ⟨x, ?_⟩
          have hy : ordIdxEquiv (Sum.inr x) = y := by rw [← hsum, Equiv.apply_symm_apply]
          rw [hcol_a x, ← hy]; rfl
    rw [Finset.union_assoc, Finset.image_union, him_res, him_ord, rw.ordPerm_union permG]
  have hentry_inj : Function.Injective (entry a) := by
    intro z₁ z₂ h
    have hp : entryPool a z₁ = entryPool a z₂ := Subtype.ext h
    exact (entryPool a).injective hp
  have hfull_sum : (∑ z ∈ full, (entry a z : ℝ)) = ∑ v ∈ rw.V_res, (v : ℝ) := by
    rw [← hfull_image, Finset.sum_image (fun x _ y _ h => hentry_inj h)]
  let μ₀ := centralEntriesMean (actualUnusedPool a full) centralPoolValue
  have hunused_card : (actualUnusedPool a full).card = n * n - full.card := by
    have hc_eq := actualUnusedPool_card n a full
    omega
  have hunused_pos : 0 < (actualUnusedPool a full).card := by
    have : 4 ≤ n * n := by nlinarith
    omega
  have hunused_sum : (∑ v ∈ actualUnusedPool a full, centralPoolValue v) =
      (Lucas.poolTotal n : ℝ) - ∑ v ∈ rw.V_res, (v : ℝ) := by
    rw [actualUnusedPool, Finset.sum_image (fun x _ y _ h => (entryPool a).injective h)]
    have hexpr : ∀ z : Cell n, centralPoolValue (entryPool a z) = (entry a z : ℝ) := fun _ => rfl
    simp only [hexpr]
    have hsdiff := Finset.sum_sdiff (f := fun z : Cell n => (entry a z : ℝ)) (Finset.subset_univ full)
    have htot : (∑ z : Cell n, (entry a z : ℝ)) = (Lucas.poolTotal n : ℝ) := by
      exact_mod_cast Lucas.placement_total n a
    linarith [hfull_sum]
  have hμ₀_bounds : (3566 / 10000 : ℝ) * X ≤ μ₀ ∧ μ₀ ≤ (5764 / 10000 : ℝ) * X := by
    have hN_pos : (0 : ℝ) < ((actualUnusedPool a full).card : ℝ) := Nat.cast_pos.mpr hunused_pos
    have hN_eq : ((actualUnusedPool a full).card : ℝ) = ((n * n : ℕ) : ℝ) - (rw.V_res.card : ℝ) := by
      rw [hunused_card, hfull_card, ← rw.hV_card,
        Nat.cast_sub (by rw [rw.hV_card, ← hfull_card]; omega)]
    have hlo_v := rw.hV_mean_lo
    have hhi_v := rw.hV_mean_hi
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hlo_v
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hhi_v
    dsimp [μ₀, centralEntriesMean]
    rw [hunused_sum]
    refine ⟨(le_div_iff₀ hN_pos).mpr ?_, (div_le_iff₀ hN_pos).mpr ?_⟩
    · rw [hN_eq]; dsimp [X]; linarith
    · rw [hN_eq]; dsimp [X]; linarith
  have hload_c : 4 * (2 * (rows.length + cols.length) + 4) ≤ n := by
    rw [hrS, hcS]; have := rw.hpack_ord; omega
  obtain ⟨c, hfixed_c, hmain_c, hanti_c, hrows_c, hcols_c⟩ :=
    ut_central_band_sharp_completion bmor imp rs lower sharp upper
      rw.hs rw.hL_ge3 hn hn_odd rw.choice rows cols hr hc hload_c a full rfl hres_le
      (by rw [hfull_image]; exact rw.hV_keepout) hμ₀_bounds.1 hμ₀_bounds.2
  -- Step 6: Center both ordinary networks (`c` -> `b₀`) and set up bounded integer flows
  let rowGap (i : Fin rows.length) (e : Fin n) : ℕ :=
    let sl := finProdFinEquiv.symm (Fin.cast hrS i)
    rw.ordGap sl.1 (false, (sl.2, e))
  let colGap (i : Fin cols.length) (e : Fin n) : ℕ :=
    let sl := finProdFinEquiv.symm (Fin.cast hcS i)
    rw.ordGap sl.1 (true, (sl.2, e))
  have hrowGap_c : ∀ i e, entry c ((rows.get i).1 e, (rows.get i).2 e) =
      entry c (e, (rows.get i).2 e) + rowGap i e := by
    intro i e
    have hlow : LayerPacking.sequenceCell rows (i, (e, false)) ∈ full := by
      refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      rw [ut_layersSupport_eq_image]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hhigh : LayerPacking.sequenceCell rows (i, (e, true)) ∈ full := by
      refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      rw [ut_layersSupport_eq_image]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    change entry c (LayerPacking.sequenceCell rows (i, (e, true))) =
      entry c (LayerPacking.sequenceCell rows (i, (e, false))) + rowGap i e
    rw [hfixed_c _ hhigh, hfixed_c _ hlow, hrow_a (i, (e, true)), hrow_a (i, (e, false))]
    exact rw.ordPerm_pair permG _ _
  have hcolGap_c : ∀ i e, entry c ((cols.get i).2 e, (cols.get i).1 e) =
      entry c ((cols.get i).2 e, e) + colGap i e := by
    intro i e
    have hlow : (LayerPacking.sequenceCell cols (i, (e, false))).swap ∈ full := by
      refine Finset.mem_union_right _ ?_
      rw [ut_transposeCells_layersSupport_eq_image]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hhigh : (LayerPacking.sequenceCell cols (i, (e, true))).swap ∈ full := by
      refine Finset.mem_union_right _ ?_
      rw [ut_transposeCells_layersSupport_eq_image]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    change entry c (LayerPacking.sequenceCell cols (i, (e, true))).swap =
      entry c (LayerPacking.sequenceCell cols (i, (e, false))).swap + colGap i e
    rw [hfixed_c _ hhigh, hfixed_c _ hlow, hcol_a (i, (e, true)), hcol_a (i, (e, false))]
    exact rw.ordPerm_pair permG _ _
  let rBlock : Fin 3 × Fin n → Finset (Fin rows.length × Fin n) :=
    prefixPairBlock rw.S (prefixPhysicalStageSlot (n := n) hrS)
  let cBlock : Fin 3 × Fin n → Finset (Fin cols.length × Fin n) :=
    prefixPairBlock rw.S (prefixPhysicalStageSlot (n := n) hcS)
  have hrGrid : ∀ e : Fin 3 × Fin n,
      EvenIntervalGrid (rBlock e) (hr.rowPairs c rowGap hrowGap_c).gap
        (rw.edgeA (false, e)) (rw.edgeRadius (false, e)) := by
    intro e
    let fEmb : Fin rw.S → Fin rows.length × Fin n := fun s => prefixPhysicalStageSlot (n := n) hrS (e, s)
    have hf_inj : Function.Injective fEmb :=
      fun s₁ s₂ h => Prod.mk.inj (prefixPhysicalStageSlot_injective (n := n) hrS h) |>.2
    have hgap_eq : ∀ s : Fin rw.S, (hr.rowPairs c rowGap hrowGap_c).gap (fEmb s) = rw.ordGap s (false, e) := by
      intro s
      change rowGap (bridgeStageLayerIndex hrS s e.1) e.2 = rw.ordGap s (false, e)
      dsimp [rowGap, bridgeStageLayerIndex]
      rw [Equiv.symm_apply_apply]
    have hg := evenIntervalGrid_image fEmb hf_inj (fun s _ => hgap_eq s) (rw.hedge_grid (false, e))
    have himg : Finset.univ.image fEmb = rBlock e := rfl
    rwa [himg] at hg
  have hcGrid : ∀ e : Fin 3 × Fin n,
      EvenIntervalGrid (cBlock e) (hc.columnPairs c colGap hcolGap_c).gap
        (rw.edgeA (true, e)) (rw.edgeRadius (true, e)) := by
    intro e
    let fEmb : Fin rw.S → Fin cols.length × Fin n := fun s => prefixPhysicalStageSlot (n := n) hcS (e, s)
    have hf_inj : Function.Injective fEmb :=
      fun s₁ s₂ h => Prod.mk.inj (prefixPhysicalStageSlot_injective (n := n) hcS h) |>.2
    have hgap_eq : ∀ s : Fin rw.S, (hc.columnPairs c colGap hcolGap_c).gap (fEmb s) = rw.ordGap s (true, e) := by
      intro s
      change colGap (bridgeStageLayerIndex hcS s e.1) e.2 = rw.ordGap s (true, e)
      dsimp [colGap, bridgeStageLayerIndex]
      rw [Equiv.symm_apply_apply]
    have hg := evenIntervalGrid_image fEmb hf_inj (fun s _ => hgap_eq s) (rw.hedge_grid (true, e))
    have himg : Finset.univ.image fEmb = cBlock e := rfl
    rwa [himg] at hg
  have hrEnd : ∀ e k, k ∈ rBlock e →
      (hr.rowPairs c rowGap hrowGap_c).low k = e.2 ∧
      (hr.rowPairs c rowGap hrowGap_c).high k = p e.1 e.2 := by
    intro e k hk
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨rfl, bridgeStageLayer_endpoints rows hrS p hrmap s e.1 e.2⟩
  have hcEnd : ∀ e k, k ∈ cBlock e →
      (hc.columnPairs c colGap hcolGap_c).low k = e.2 ∧
      (hc.columnPairs c colGap hcolGap_c).high k = p e.1 e.2 := by
    intro e k hk
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨rfl, bridgeStageLayer_endpoints cols hcS p hcmap s e.1 e.2⟩
  have hWX_nn : 0 ≤ (utWOrd n : ℝ) * X := by positivity
  let C_half : ℕ := ⌊((350 / 1000 : ℝ) + (232 / 1000 : ℝ) * (utWOrd n : ℝ)) * X⌋₊
  let N_cap : ℕ := 2 * C_half
  have hC_half_le : (C_half : ℝ) ≤ (350 / 1000 : ℝ) * X + (232 / 1000 : ℝ) * ((utWOrd n : ℝ) * X) := by
    have h : (C_half : ℝ) ≤ ((350 / 1000 : ℝ) + (232 / 1000 : ℝ) * (utWOrd n : ℝ)) * X :=
      Nat.floor_le (by positivity)
    linarith [show ((350 / 1000 : ℝ) + (232 / 1000 : ℝ) * (utWOrd n : ℝ)) * X =
      (350 / 1000 : ℝ) * X + (232 / 1000 : ℝ) * ((utWOrd n : ℝ) * X) by ring]
  have hC_half_gt : (350 / 1000 : ℝ) * X + (232 / 1000 : ℝ) * ((utWOrd n : ℝ) * X) - 1 < (C_half : ℝ) := by
    have h : ((350 / 1000 : ℝ) + (232 / 1000 : ℝ) * (utWOrd n : ℝ)) * X - 1 < (C_half : ℝ) :=
      Nat.sub_one_lt_floor _
    linarith [show ((350 / 1000 : ℝ) + (232 / 1000 : ℝ) * (utWOrd n : ℝ)) * X =
      (350 / 1000 : ℝ) * X + (232 / 1000 : ℝ) * ((utWOrd n : ℝ) * X) by ring]
  have hedge_cap_gate : ∀ u : UTEdge n, rw.edgeA u + 2 * (N_cap / 2) ≤ evenGridCenter (rw.edgeRadius u) := by
    intro u
    have hdiv : N_cap / 2 = C_half := Nat.mul_div_right C_half (by decide)
    rw [hdiv]
    have hcent := evenGridCenter_midpoint_error (rw.edgeRadius u) (rw.hedge_even u)
    have hcent_R : (rw.edgeRadius u : ℝ) ≤ 2 * (evenGridCenter (rw.edgeRadius u) : ℝ) + 2 := by
      exact_mod_cast (show rw.edgeRadius u ≤ 2 * evenGridCenter (rw.edgeRadius u) + 2 by
        clear * - hcent; omega)
    have hspan_raw := rw.hedge_span u
    have hspan : (1467 / 1000 : ℝ) * X + (932 / 1000 : ℝ) * ((utWOrd n : ℝ) * X) ≤
        (rw.edgeRadius u : ℝ) - (rw.edgeA u : ℝ) := by
      dsimp [X] at hspan_raw ⊢
      linarith [show (1467 / 1000 + (932 / 1000 : ℝ) * (utWOrd n : ℝ)) * utX n =
        (1467 / 1000 : ℝ) * utX n + (932 / 1000 : ℝ) * ((utWOrd n : ℝ) * utX n) by ring]
    have hAub : (rw.edgeA u : ℝ) ≤ (12 / 10000 : ℝ) * ((utWOrd n : ℝ) * X) := by
      have h1 := rw.hedgeA_ub u
      have h2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hH0Max_le_WOrd (by norm_num : (0 : ℝ) ≤ 12 / 10000)) hX_pos.le
      dsimp [X] at h2 ⊢; linarith
    have hgoal_R : (rw.edgeA u : ℝ) + 2 * (C_half : ℝ) ≤ (evenGridCenter (rw.edgeRadius u) : ℝ) := by
      have hX_lb : (283 / 100 : ℝ) * 10 ^ 10 ≤ X := by dsimp [X, utX]; linarith [hX_283]
      linarith
    exact_mod_cast hgoal_R
  obtain ⟨b₀, hrinvoice, hcinvoice, hm₀, ha₀, hfixed₀, hflows⟩ :=
    twoNetworks_realize_bounded_integer_flows_of_evenIntervalGrid c reserved rows cols hr hc
      rowGap colGap hrowGap_c hcolGap_c rBlock cBlock
      (fun e => rw.edgeA (false, e)) (fun e => rw.edgeRadius (false, e))
      (fun e => rw.edgeA (true, e)) (fun e => rw.edgeRadius (true, e))
      Prod.snd (fun e => p e.1 e.2) Prod.snd (fun e => p e.1 e.2)
      (fun e f h => prefixPairBlock_disjoint rw.S (prefixPhysicalStageSlot (n := n) hrS)
        (prefixPhysicalStageSlot_injective (n := n) hrS) e f h)
      (fun e f h => prefixPairBlock_disjoint rw.S (prefixPhysicalStageSlot (n := n) hcS)
        (prefixPhysicalStageSlot_injective (n := n) hcS) e f h)
      hrGrid hcGrid hrEnd hcEnd N_cap
      (fun e => hedge_cap_gate (false, e)) (fun e => hedge_cap_gate (true, e))
  -- Step 7: Select `D = y / 1400` T75 targets and bound row/column demands on `b₀`
  let m : ℝ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
  let y : ℝ := (n : ℝ) * m
  obtain ⟨t_vec, ht_sum, ht_props⟩ := upper_tail_t75_targets_1400 bmor imp rs hMV sharp upper hn hn_odd
  have hm_hi : m < (519 / 1000 : ℝ) * X := by
    have hmb := global_pool_mean_bounds rs sharp (by clear * - hn; omega : 2001 ≤ n)
    dsimp [m, X, utX]
    rw [prescribedPoolValues_mean]
    exact (div_lt_iff₀ (by dsimp [X, utX] at hX_pos; exact hX_pos)).mp hmb.2
  have hD_t75_ub : y / 1400 ≤ (160 / 1000 : ℝ) * ((utWOrd n : ℝ) * X) := by
    have hy_ub : y ≤ (519 / 1000 : ℝ) * ((n : ℝ) * X) := by
      have hm1 := mul_le_mul_of_nonneg_left hm_hi.le (Nat.cast_nonneg n)
      dsimp [y]; linarith
    have hnW : (n : ℝ) * X ≤ 430 * ((utWOrd n : ℝ) * X) := by
      have h := mul_le_mul_of_nonneg_right hn_le_WOrd hX_pos.le
      linarith
    linarith
  have hpool_eq_ny : (Lucas.poolTotal n : ℝ) = (n : ℝ) * y := by
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn_pos)
    dsimp [y, m]
    rw [prescribedPoolValues_mean]
    push_cast; field_simp
  let sumGap (u : UTEdge n) : ℕ := ∑ s : Fin rw.S, rw.ordGap s u
  let R_div_row (r : Fin n) : ℝ :=
    (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
      (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (sumGap (false, e) : ℤ)) e r : ℝ)
  let R_div_col (col : Fin n) : ℝ :=
    (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
      (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (sumGap (true, e) : ℤ)) e col : ℝ)
  let M_row_ideal (r : Fin n) : ℝ :=
    (∑ z ∈ rowCells r ∩ full, (entry a z : ℝ)) + ((rowCells r \ full).card : ℝ) * μ₀ + R_div_row r
  let M_col_ideal (col : Fin n) : ℝ :=
    (∑ z ∈ columnCells col ∩ full, (entry a z : ℝ)) + ((columnCells col \ full).card : ℝ) * μ₀ + R_div_col col
  have hdiv_zero : ∀ f : Fin 3 × Fin n → ℕ,
      (∑ r : Fin n, (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
        (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (f e : ℤ)) e r : ℝ)) = 0 := by
    intro f
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hper_e : ∀ e : Fin 3 × Fin n,
        (∑ r : Fin n, (edgeTransfer Prod.snd (fun x : Fin 3 × Fin n => p x.1 x.2)
          (fun x => (f x : ℤ)) e r : ℝ)) = 0 := by
      intro e
      have hcast_e : ∀ r : Fin n,
          (edgeTransfer Prod.snd (fun x : Fin 3 × Fin n => p x.1 x.2)
            (fun x => (f x : ℤ)) e r : ℝ) =
          (if e.2 = r then (f e : ℝ) else 0) - (if p e.1 e.2 = r then (f e : ℝ) else 0) := by
        intro r; unfold edgeTransfer; split_ifs <;> push_cast <;> ring
      simp [hcast_e, Finset.sum_sub_distrib]
    simp [hper_e]
  have hμ₀_mul_eq : ((Finset.univ \ full).card : ℝ) * μ₀ =
      (Lucas.poolTotal n : ℝ) - ∑ z ∈ full, (entry a z : ℝ) := by
    have hcard_eq : (Finset.univ \ full).card = (actualUnusedPool a full).card := by
      rw [actualUnusedPool, Finset.card_image_of_injective _ (entryPool a).injective]
    have hN_ne : ((actualUnusedPool a full).card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hunused_pos)
    rw [hcard_eq]; dsimp [μ₀, centralEntriesMean]
    rw [hunused_sum, ← hfull_sum, mul_div_cancel₀ _ hN_ne]
  have hrow_ideal_sum : ∑ r : Fin n, M_row_ideal r = (n : ℝ) * y := by
    have hpart : ∀ (f : Cell n → ℝ) (T : Finset (Cell n)),
        (∑ r : Fin n, ∑ z ∈ rowCells r ∩ T, f z) = ∑ z ∈ T, f z := by
      intro f T
      have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n))) (fun r => rowCells r ∩ T) := by
        intro r₁ _ r₂ _ hne; apply Finset.disjoint_left.mpr; intro z hz1 hz2
        exact hne ((mem_rowCells r₁ z |>.mp (Finset.mem_inter.mp hz1).1).symm.trans
          (mem_rowCells r₂ z |>.mp (Finset.mem_inter.mp hz2).1))
      have hun : Finset.univ.biUnion (fun r => rowCells r ∩ T) = T := by ext z; simp
      rw [← Finset.sum_biUnion hdis, hun]
    dsimp [M_row_ideal, R_div_row]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hdiv_zero, add_zero, hpart _ full, ← Finset.sum_mul]
    have hcards : (∑ r : Fin n, ((rowCells r \ full).card : ℝ)) = ((Finset.univ \ full).card : ℝ) := by
      have heq_sd : ∀ r : Fin n, ((rowCells r \ full).card : ℝ) = ∑ _z ∈ rowCells r ∩ (Finset.univ \ full), (1 : ℝ) := by
        intro r
        have hs : rowCells r \ full = rowCells r ∩ (Finset.univ \ full) := by ext z; simp
        rw [hs, Finset.sum_const, nsmul_eq_mul, mul_one]
      simp only [heq_sd]; rw [hpart _ (Finset.univ \ full), Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcards, hμ₀_mul_eq, ← hpool_eq_ny]; ring
  have hcol_ideal_sum : ∑ col : Fin n, M_col_ideal col = (n : ℝ) * y := by
    have hpart : ∀ (f : Cell n → ℝ) (T : Finset (Cell n)),
        (∑ col : Fin n, ∑ z ∈ columnCells col ∩ T, f z) = ∑ z ∈ T, f z := by
      intro f T
      have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n))) (fun col => columnCells col ∩ T) := by
        intro c₁ _ c₂ _ hne; apply Finset.disjoint_left.mpr; intro z hz1 hz2
        exact hne ((mem_columnCells c₁ z |>.mp (Finset.mem_inter.mp hz1).1).symm.trans
          (mem_columnCells c₂ z |>.mp (Finset.mem_inter.mp hz2).1))
      have hun : Finset.univ.biUnion (fun col => columnCells col ∩ T) = T := by ext z; simp
      rw [← Finset.sum_biUnion hdis, hun]
    dsimp [M_col_ideal, R_div_col]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hdiv_zero, add_zero, hpart _ full, ← Finset.sum_mul]
    have hcards : (∑ col : Fin n, ((columnCells col \ full).card : ℝ)) = ((Finset.univ \ full).card : ℝ) := by
      have heq_sd : ∀ col : Fin n, ((columnCells col \ full).card : ℝ) = ∑ _z ∈ columnCells col ∩ (Finset.univ \ full), (1 : ℝ) := by
        intro col
        have hs : columnCells col \ full = columnCells col ∩ (Finset.univ \ full) := by ext z; simp
        rw [hs, Finset.sum_const, nsmul_eq_mul, mul_one]
      simp only [heq_sd]; rw [hpart _ (Finset.univ \ full), Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcards, hμ₀_mul_eq, ← hpool_eq_ny]; ring
  -- Growth sum & balanced discrepancy `K_growth`
  let K_growth : ℝ :=
    ∑ g ∈ slotsG.image Prod.fst, 12 * prefixOriginalStageMean slotsG Prod.fst xVal g
  let growthLine (line : Fin n ⊕ Fin n) : ℝ :=
    ∑ gu : Fin rw.G × UTEdge n, wLine line gu * xVal (gu.1, permG gu.1 gu.2)
  have hw_stage_sum : ∀ (line : Fin n ⊕ Fin n) (g : Fin rw.G),
      (∑ s ∈ slotsG.filter (fun s => s.1 = g), wLine line s) = 12 := by
    intro line g
    have hf_eq : slotsG.filter (fun s => s.1 = g) = (Finset.univ : Finset (UTEdge n)).image (fun u => (g, u)) := by
      ext ⟨g', u⟩; simp [slotsG, eq_comm]
    rw [hf_eq, Finset.sum_image (fun _ _ _ _ h => congrArg Prod.snd h),
      Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_prod_type, Fintype.sum_prod_type]
    cases line with
    | inl r =>
      dsimp [wLine]
      have h1 : ∀ l : Fin 3, (∑ e : Fin n, ((if e = r then (1 : ℝ) else 0) + (if p l e = r then 1 else 0))) = 2 := by
        intro l
        rw [Finset.sum_add_distrib]
        have ha : (∑ e : Fin n, if e = r then (1 : ℝ) else 0) = 1 := by simp [Finset.sum_ite_eq']
        have hb : (∑ e : Fin n, if p l e = r then (1 : ℝ) else 0) = 1 := by
          rw [← Equiv.sum_comp (p l).symm]; simp [Finset.sum_ite_eq']
        linarith
      have h2 : ∀ l : Fin 3, (∑ e : Fin n, if gc (gStage g) l e = r then (2 : ℝ) else 0) = 2 := by
        intro l; rw [← Equiv.sum_comp (gc (gStage g) l).symm]; simp [Finset.sum_ite_eq']
      simp [h1, h2]; norm_num
    | inr col =>
      dsimp [wLine]
      have h1 : ∀ l : Fin 3, (∑ e : Fin n, if gr (gStage g) l e = col then (2 : ℝ) else 0) = 2 := by
        intro l; rw [← Equiv.sum_comp (gr (gStage g) l).symm]; simp [Finset.sum_ite_eq']
      have h2 : ∀ l : Fin 3, (∑ e : Fin n, ((if e = col then (1 : ℝ) else 0) + (if p l e = col then 1 else 0))) = 2 := by
        intro l
        rw [Finset.sum_add_distrib]
        have ha : (∑ e : Fin n, if e = col then (1 : ℝ) else 0) = 1 := by simp [Finset.sum_ite_eq']
        have hb : (∑ e : Fin n, if p l e = col then (1 : ℝ) else 0) = 1 := by
          rw [← Equiv.sum_comp (p l).symm]; simp [Finset.sum_ite_eq']
        linarith
      simp [h1, h2]; norm_num
  have hgrowth_bal : ∀ line : Fin n ⊕ Fin n,
      |growthLine line - K_growth| ≤ ((8192 / 1000 : ℝ) + (136 / 1000 : ℝ) * (utWOrd n : ℝ)) * X := by
    intro line
    have hb := he_bal line (Finset.mem_univ line)
    have hattach_eq : (∑ s : {s // s ∈ slotsG}, wLine line s.val * xVal (e_assign s).val) = growthLine line := by
      rw [← Equiv.sum_comp e_univ.symm]
      apply Finset.sum_congr rfl; intro gu _
      have he_val : (e_assign (e_univ.symm gu)).val = (gu.1, permG gu.1 gu.2) := by
        change e0 gu = _; exact he0_eq gu.1 gu.2
      rw [he_val]; rfl
    have hK_eq : (∑ g ∈ slotsG.image Prod.fst,
        (∑ s ∈ slotsG.filter (fun s => s.1 = g), wLine line s) *
          prefixOriginalStageMean slotsG Prod.fst xVal g) = K_growth :=
      Finset.sum_congr rfl fun g _ => by rw [hw_stage_sum line g]
    rw [hattach_eq, hK_eq] at hb
    have hclog_R : (Nat.clog 2 (6 * n) : ℝ) ≤ (utLn n : ℝ) + 8 := by exact_mod_cast hclog
    have hLn_W : (utLn n : ℝ) ≤ (4730 / 35735 : ℝ) * (utWOrd n : ℝ) := by linarith [hLn11_lin, hn_le_WOrd]
    have h8C : 8 * utMidWidth n = (1024 / 1000 : ℝ) * X := by dsimp [utMidWidth, X]; ring
    have hprod_le : (Nat.clog 2 (6 * n) : ℝ) * (8 * utMidWidth n) ≤
        (8192 / 1000 : ℝ) * X + (136 / 1000 : ℝ) * ((utWOrd n : ℝ) * X) := by
      rw [h8C]
      have hm1 := mul_le_mul_of_nonneg_right hclog_R (by positivity : (0 : ℝ) ≤ (1024 / 1000 : ℝ) * X)
      have hm2 := mul_le_mul_of_nonneg_right hLn_W hX_pos.le
      have hexp_ring : ((utLn n : ℝ) + 8) * ((1024 / 1000 : ℝ) * X) =
          (1024 / 1000 : ℝ) * ((utLn n : ℝ) * X) + (8192 / 1000 : ℝ) * X := by ring
      linarith
    have hrhs_eq : ((8192 / 1000 : ℝ) + (136 / 1000 : ℝ) * (utWOrd n : ℝ)) * X =
        (8192 / 1000 : ℝ) * X + (136 / 1000 : ℝ) * ((utWOrd n : ℝ) * X) := by ring
    rw [hrhs_eq]
    exact hb.trans hprod_le
  have himg_fst : slotsG.image Prod.fst = Finset.univ := by
    ext g; simp only [slotsG, Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact ⟨(g, (false, (0, ⟨0, hn_pos⟩))), rfl⟩
  have hK_mul_n : (n : ℝ) * K_growth = ∑ g : Fin rw.G, 2 * ∑ u : UTEdge n, xVal (g, u) := by
    dsimp [K_growth]
    rw [himg_fst, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro g _
    dsimp [prefixOriginalStageMean]
    have hf_eq : slotsG.filter (fun v => v.1 = g) = (Finset.univ : Finset (UTEdge n)).image (fun u => (g, u)) := by
      ext ⟨g', u⟩; simp [slotsG, eq_comm]
    rw [hslots_filter_card g, hf_eq, Finset.sum_image (fun _ _ _ _ h => congrArg Prod.snd h)]
    have h6n_ne : ((6 * n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : 6 * n ≠ 0)
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn_pos)
    push_cast; field_simp; ring
  have hgrowth_row_sum : (∑ r : Fin n, growthLine (Sum.inl r)) = (n : ℝ) * K_growth := by
    dsimp [growthLine]
    rw [Finset.sum_comm, Fintype.sum_prod_type, hK_mul_n]
    apply Finset.sum_congr rfl; intro g _
    have hper_u : ∀ u : UTEdge n,
        (∑ r : Fin n, wLine (Sum.inl r) (g, u) * xVal (g, permG g u)) = 2 * xVal (g, permG g u) := by
      rintro ⟨b, l, e⟩
      rw [← Finset.sum_mul]
      cases b <;> dsimp [wLine]
      · simp [Finset.sum_add_distrib, Finset.sum_ite_eq]; norm_num
      · simp [Finset.sum_ite_eq]
    simp only [hper_u, ← Finset.mul_sum]
    congr 1
    exact Equiv.sum_comp (permG g) (fun u => xVal (g, u))
  have hgrowth_col_sum : (∑ col : Fin n, growthLine (Sum.inr col)) = (n : ℝ) * K_growth := by
    dsimp [growthLine]
    rw [Finset.sum_comm, Fintype.sum_prod_type, hK_mul_n]
    apply Finset.sum_congr rfl; intro g _
    have hper_u : ∀ u : UTEdge n,
        (∑ col : Fin n, wLine (Sum.inr col) (g, u) * xVal (g, permG g u)) = 2 * xVal (g, permG g u) := by
      rintro ⟨b, l, e⟩
      rw [← Finset.sum_mul]
      cases b <;> dsimp [wLine]
      · simp [Finset.sum_ite_eq]
      · simp [Finset.sum_add_distrib, Finset.sum_ite_eq]; norm_num
    simp only [hper_u, ← Finset.mul_sum]
    congr 1
    exact Equiv.sum_comp (permG g) (fun u => xVal (g, u))
  -- Identify Growth stages inside `ut_row_ord_midpoint_eq` and `ut_col_ord_midpoint_eq`
  have hgrowth_row_stage : ∀ (r : Fin n) (g : Fin rw.G),
      (∑ l : Fin 3,
        (((rw.ordPerm permG (gStage g) (false, (l, r)) false +
            rw.ordPerm permG (gStage g) (false, (l, r)) true : ℕ) : ℝ) / 2 +
         ((rw.ordPerm permG (gStage g) (false, (l, (p l).symm r)) false +
            rw.ordPerm permG (gStage g) (false, (l, (p l).symm r)) true : ℕ) : ℝ) / 2 +
         ((rw.ordPerm permG (gStage g) (true, (l, (gc (gStage g) l).symm r)) false +
            rw.ordPerm permG (gStage g) (true, (l, (gc (gStage g) l).symm r)) true : ℕ) : ℝ))) =
      ∑ u : UTEdge n, wLine (Sum.inl r) (g, u) * xVal (g, permG g u) := by
    intro r g
    have hord_x : ∀ u : UTEdge n,
        (((rw.ordPerm permG (gStage g) u false + rw.ordPerm permG (gStage g) u true : ℕ) : ℝ)) / 2 =
        xVal (g, permG g u) := by
      intro u; dsimp [UTRoleWitness.ordPerm, gStage, xVal]; rw [if_pos g.isLt, if_pos g.isLt]
    have hord_x2 : ∀ u : UTEdge n,
        (((rw.ordPerm permG (gStage g) u false + rw.ordPerm permG (gStage g) u true : ℕ) : ℝ)) =
        2 * xVal (g, permG g u) := by
      intro u; linarith [hord_x u]
    simp only [hord_x2]
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_prod_type, Fintype.sum_prod_type]
    have hfalse : (∑ l : Fin 3, ∑ e : Fin n, wLine (Sum.inl r) (g, (false, (l, e))) * xVal (g, permG g (false, (l, e)))) =
        ∑ l : Fin 3, (xVal (g, permG g (false, (l, r))) + xVal (g, permG g (false, (l, (p l).symm r)))) := by
      apply Finset.sum_congr rfl; intro l _
      dsimp [wLine]
      simp only [add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
      congr 1
      rw [← Equiv.sum_comp (p l).symm]
      simp [Finset.sum_ite_eq']
    have htrue : (∑ l : Fin 3, ∑ e : Fin n, wLine (Sum.inl r) (g, (true, (l, e))) * xVal (g, permG g (true, (l, e)))) =
        ∑ l : Fin 3, 2 * xVal (g, permG g (true, (l, (gc (gStage g) l).symm r))) := by
      apply Finset.sum_congr rfl; intro l _
      dsimp [wLine]
      rw [← Equiv.sum_comp (gc (gStage g) l).symm]
      simp [ite_mul, Finset.sum_ite_eq']
    rw [hfalse, htrue, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro l _; ring
  have hgrowth_col_stage : ∀ (col : Fin n) (g : Fin rw.G),
      (∑ l : Fin 3,
        (((rw.ordPerm permG (gStage g) (false, (l, (gr (gStage g) l).symm col)) false +
            rw.ordPerm permG (gStage g) (false, (l, (gr (gStage g) l).symm col)) true : ℕ) : ℝ) +
         ((rw.ordPerm permG (gStage g) (true, (l, col)) false +
            rw.ordPerm permG (gStage g) (true, (l, col)) true : ℕ) : ℝ) / 2 +
         ((rw.ordPerm permG (gStage g) (true, (l, (p l).symm col)) false +
            rw.ordPerm permG (gStage g) (true, (l, (p l).symm col)) true : ℕ) : ℝ) / 2)) =
      ∑ u : UTEdge n, wLine (Sum.inr col) (g, u) * xVal (g, permG g u) := by
    intro col g
    have hord_x : ∀ u : UTEdge n,
        (((rw.ordPerm permG (gStage g) u false + rw.ordPerm permG (gStage g) u true : ℕ) : ℝ)) / 2 =
        xVal (g, permG g u) := by
      intro u; dsimp [UTRoleWitness.ordPerm, gStage, xVal]; rw [if_pos g.isLt, if_pos g.isLt]
    have hord_x2 : ∀ u : UTEdge n,
        (((rw.ordPerm permG (gStage g) u false + rw.ordPerm permG (gStage g) u true : ℕ) : ℝ)) =
        2 * xVal (g, permG g u) := by
      intro u; linarith [hord_x u]
    simp only [hord_x2]
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_prod_type, Fintype.sum_prod_type]
    have hfalse : (∑ l : Fin 3, ∑ e : Fin n, wLine (Sum.inr col) (g, (false, (l, e))) * xVal (g, permG g (false, (l, e)))) =
        ∑ l : Fin 3, 2 * xVal (g, permG g (false, (l, (gr (gStage g) l).symm col))) := by
      apply Finset.sum_congr rfl; intro l _
      dsimp [wLine]
      rw [← Equiv.sum_comp (gr (gStage g) l).symm]
      simp [ite_mul, Finset.sum_ite_eq']
    have htrue : (∑ l : Fin 3, ∑ e : Fin n, wLine (Sum.inr col) (g, (true, (l, e))) * xVal (g, permG g (true, (l, e)))) =
        ∑ l : Fin 3, (xVal (g, permG g (true, (l, col))) + xVal (g, permG g (true, (l, (p l).symm col)))) := by
      apply Finset.sum_congr rfl; intro l _
      dsimp [wLine]
      simp only [add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
      congr 1
      rw [← Equiv.sum_comp (p l).symm]
      simp [Finset.sum_ite_eq']
    rw [hfalse, htrue, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro l _; ring
  -- Bound `|M_rest_row r - (y - K_growth)|` and `|M_rest_col col - (y - K_growth)|`
  let M_rest_row (r : Fin n) : ℝ := M_row_ideal r - growthLine (Sum.inl r)
  let M_rest_col (col : Fin n) : ℝ := M_col_ideal col - growthLine (Sum.inr col)
  have hS_split : ∀ f : Fin rw.S → ℝ,
      (∑ s : Fin rw.S, f s) = (∑ g : Fin rw.G, f (gStage g)) +
        ∑ s ∈ (Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val), f s := by
    intro f
    have hlt_eq : (Finset.univ : Finset (Fin rw.S)).filter (fun s => s.val < rw.G) =
        Finset.univ.image gStage := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, gStage, Fin.ext_iff]
      exact ⟨fun h => ⟨⟨s.val, h⟩, rfl⟩, fun ⟨g, hg⟩ => by rw [← hg]; exact g.isLt⟩
    have hdis : Disjoint ((Finset.univ : Finset (Fin rw.S)).filter (fun s => s.val < rw.G))
        ((Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val)) := by
      rw [Finset.disjoint_left]; intro s h1 h2
      have a1 := (Finset.mem_filter.mp h1).2
      have a2 := (Finset.mem_filter.mp h2).2
      clear * - a1 a2; omega
    have hun : ((Finset.univ : Finset (Fin rw.S)).filter (fun s => s.val < rw.G)) ∪
        ((Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val)) = Finset.univ := by
      ext s; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      clear * -; omega
    have hgStage_inj : ∀ g₁ ∈ (Finset.univ : Finset (Fin rw.G)),
        ∀ g₂ ∈ (Finset.univ : Finset (Fin rw.G)), gStage g₁ = gStage g₂ → g₁ = g₂ := by
      intro g₁ _ g₂ _ h
      exact Fin.ext (congrArg (Fin.val : Fin rw.S → ℕ) h)
    conv_lhs => rw [← hun]
    rw [Finset.sum_union hdis, hlt_eq, Finset.sum_image (f := f) (g := gStage) hgStage_inj]
  have hμ₀_nn : 0 ≤ μ₀ := by linarith [hμ₀_bounds.1]
  have hμ₀_le_X : μ₀ ≤ X := by linarith [hμ₀_bounds.2]
  have hnongrowth_pair : ∀ (s : Fin rw.S), rw.G ≤ s.val → ∀ u : UTEdge n,
      |(((rw.ordPerm permG s u false + rw.ordPerm permG s u true : ℕ) : ℝ) - rw.ordNongrowthAnchor s)| ≤
        rw.ordNongrowthHalfWidth s := by
    intro s hs u
    have hnlt : ¬ (s.val < rw.G) := by clear * - hs; omega
    dsimp [UTRoleWitness.ordPerm]
    rw [dif_neg hnlt, dif_neg hnlt]
    exact rw.hnongrowth_pair_bound s hs u
  have hM_rest_row_anchor : ∀ r : Fin n,
      ∃ rectTerm : ℝ, 0 ≤ rectTerm ∧ rectTerm ≤ 2 * X ∧
        |(M_rest_row r - (((n - 12 * rw.S - 2 : ℕ) : ℝ) * μ₀ + rectTerm +
            ∑ s ∈ (Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val),
              6 * rw.ordNongrowthAnchor s))| ≤
          ∑ s : Fin rw.S, 6 * rw.ordNongrowthHalfWidth s := by
    intro r
    have hrect_b := ut_row_rect_term_bounds rw.hs rw.choice a hμ₀_nn hμ₀_le_X r
    have hd1 : Disjoint (rowCells r ∩ reserved) (rowCells r ∩ LayerPacking.layersSupport rows) :=
      hdis_res_r.mono Finset.inter_subset_right Finset.inter_subset_right
    have hd2 : Disjoint ((rowCells r ∩ reserved) ∪ (rowCells r ∩ LayerPacking.layersSupport rows))
        (rowCells r ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
      rw [← Finset.inter_union_distrib_left]
      exact hdis_res_c.mono Finset.inter_subset_right Finset.inter_subset_right
    have hsplit_r : rowCells r ∩ full = (rowCells r ∩ reserved) ∪
        (rowCells r ∩ LayerPacking.layersSupport rows) ∪
        (rowCells r ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
      dsimp [full]; rw [Finset.inter_union_distrib_left, Finset.inter_union_distrib_left]
    have hcard_r_layers : (rowCells r ∩ LayerPacking.layersSupport rows).card = 6 * rw.S ∧
        (rowCells r ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols)).card = 6 * rw.S := by
      have heq1 : rowCells r ∩ LayerPacking.layersSupport rows =
          (LayerPacking.layersSupport rows).filter (fun z => z.1 = r) := by ext z; simp [and_comm]
      have heq2 : rowCells r ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols) =
          (LayerPacking.transposeCells (LayerPacking.layersSupport cols)).filter (fun z => z.1 = r) := by
        ext z; simp [and_comm]
      rw [heq1, heq2, (hrow_layer_cards r).1, (hrow_layer_cards r).2, hlen_p]
      exact ⟨by ring, by ring⟩
    have hsdiff_card : (rowCells r \ full).card = (n - 12 * rw.S - 2) + (2 - (rowCells r ∩ reserved).card) := by
      have htot_r := Finset.card_sdiff_add_card_inter (rowCells r) full
      have hrc_n : (rowCells r).card = n := by
        dsimp [rowCells]; rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h)]; simp
      have hfull_r : (rowCells r ∩ full).card = (rowCells r ∩ reserved).card + 12 * rw.S := by
        rw [hsplit_r, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
          hcard_r_layers.1, hcard_r_layers.2]; ring
      have hq2 : (rowCells r ∩ reserved).card ≤ 2 := hrect_b.1
      have h12S : 12 * rw.S + 2 ≤ n := by have h := rw.hpack_ord; clear * - h; omega
      clear * - htot_r hrc_n hfull_r hq2 h12S; omega
    have hord_eq := ut_row_ord_midpoint_eq p rows cols hrS hcS hrmap hr hc a
      (rw.ordPerm permG) rw.ordGap (fun s l e => rw.ordPerm_pair permG s (false, (l, e)))
      hrow_a hcol_a (fun e => sumGap (false, e)) (fun _ => rfl) r
    let rectTerm := (∑ z ∈ rowCells r ∩ reserved, (entry a z : ℝ)) +
      ((2 - (rowCells r ∩ reserved).card : ℕ) : ℝ) * μ₀
    refine ⟨rectTerm, hrect_b.2.1, hrect_b.2.2, ?_⟩
    have hM_eq : M_rest_row r = ((n - 12 * rw.S - 2 : ℕ) : ℝ) * μ₀ + rectTerm +
        ∑ s ∈ (Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val),
          ∑ l : Fin 3,
            (let gc_l := (cols.get (bridgeStageLayerIndex hcS s l)).2
             (((rw.ordPerm permG s (false, (l, r)) false + rw.ordPerm permG s (false, (l, r)) true : ℕ) : ℝ) / 2 +
              ((rw.ordPerm permG s (false, (l, (p l).symm r)) false + rw.ordPerm permG s (false, (l, (p l).symm r)) true : ℕ) : ℝ) / 2 +
              ((rw.ordPerm permG s (true, (l, gc_l.symm r)) false + rw.ordPerm permG s (true, (l, gc_l.symm r)) true : ℕ) : ℝ))) := by
      dsimp [M_rest_row, M_row_ideal, R_div_row]
      rw [hsplit_r, Finset.sum_union hd2, Finset.sum_union hd1, hsdiff_card, Nat.cast_add]
      have hrearr : (∑ x ∈ rowCells r ∩ reserved, (entry a x : ℝ)) +
          (∑ x ∈ rowCells r ∩ LayerPacking.layersSupport rows, (entry a x : ℝ)) +
          (∑ x ∈ rowCells r ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols), (entry a x : ℝ)) +
          (((n - 12 * rw.S - 2 : ℕ) : ℝ) + ((2 - (rowCells r ∩ reserved).card : ℕ) : ℝ)) * μ₀ +
          (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
            (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (sumGap (false, e) : ℤ)) e r : ℝ) =
          ((n - 12 * rw.S - 2 : ℕ) : ℝ) * μ₀ + rectTerm +
          ((∑ x ∈ rowCells r ∩ LayerPacking.layersSupport rows, (entry a x : ℝ)) +
           (∑ x ∈ rowCells r ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols), (entry a x : ℝ)) +
           (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
             (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (sumGap (false, e) : ℤ)) e r : ℝ)) := by
        dsimp [rectTerm]; ring
      rw [hrearr, hord_eq, hS_split]
      have hg_eq : (∑ g : Fin rw.G, ∑ l : Fin 3,
          (((rw.ordPerm permG (gStage g) (false, (l, r)) false + rw.ordPerm permG (gStage g) (false, (l, r)) true : ℕ) : ℝ) / 2 +
           ((rw.ordPerm permG (gStage g) (false, (l, (p l).symm r)) false + rw.ordPerm permG (gStage g) (false, (l, (p l).symm r)) true : ℕ) : ℝ) / 2 +
           ((rw.ordPerm permG (gStage g) (true, (l, (gc (gStage g) l).symm r)) false + rw.ordPerm permG (gStage g) (true, (l, (gc (gStage g) l).symm r)) true : ℕ) : ℝ))) =
          growthLine (Sum.inl r) := by
        dsimp [growthLine]
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun g _ => hgrowth_row_stage r g
      rw [hg_eq]; dsimp [rectTerm]; ring
    rw [hM_eq]
    have hsub_eq : (((n - 12 * rw.S - 2 : ℕ) : ℝ) * μ₀ + rectTerm +
        ∑ s ∈ (Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val),
          ∑ l : Fin 3,
            (let gc_l := (cols.get (bridgeStageLayerIndex hcS s l)).2
             (((rw.ordPerm permG s (false, (l, r)) false + rw.ordPerm permG s (false, (l, r)) true : ℕ) : ℝ) / 2 +
              ((rw.ordPerm permG s (false, (l, (p l).symm r)) false + rw.ordPerm permG s (false, (l, (p l).symm r)) true : ℕ) : ℝ) / 2 +
              ((rw.ordPerm permG s (true, (l, gc_l.symm r)) false + rw.ordPerm permG s (true, (l, gc_l.symm r)) true : ℕ) : ℝ)))) -
        (((n - 12 * rw.S - 2 : ℕ) : ℝ) * μ₀ + rectTerm +
          ∑ s ∈ (Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val),
            6 * rw.ordNongrowthAnchor s) =
        ∑ s ∈ (Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val),
          ((∑ l : Fin 3,
            (let gc_l := (cols.get (bridgeStageLayerIndex hcS s l)).2
             (((rw.ordPerm permG s (false, (l, r)) false + rw.ordPerm permG s (false, (l, r)) true : ℕ) : ℝ) / 2 +
              ((rw.ordPerm permG s (false, (l, (p l).symm r)) false + rw.ordPerm permG s (false, (l, (p l).symm r)) true : ℕ) : ℝ) / 2 +
              ((rw.ordPerm permG s (true, (l, gc_l.symm r)) false + rw.ordPerm permG s (true, (l, gc_l.symm r)) true : ℕ) : ℝ)))) -
           6 * rw.ordNongrowthAnchor s) := by
      rw [Finset.sum_sub_distrib]; ring
    rw [hsub_eq]
    calc |∑ s ∈ (Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val),
          ((∑ l : Fin 3,
            (let gc_l := (cols.get (bridgeStageLayerIndex hcS s l)).2
             (((rw.ordPerm permG s (false, (l, r)) false + rw.ordPerm permG s (false, (l, r)) true : ℕ) : ℝ) / 2 +
              ((rw.ordPerm permG s (false, (l, (p l).symm r)) false + rw.ordPerm permG s (false, (l, (p l).symm r)) true : ℕ) : ℝ) / 2 +
              ((rw.ordPerm permG s (true, (l, gc_l.symm r)) false + rw.ordPerm permG s (true, (l, gc_l.symm r)) true : ℕ) : ℝ)))) -
           6 * rw.ordNongrowthAnchor s)|
        ≤ ∑ s ∈ (Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val),
            |((∑ l : Fin 3,
              (let gc_l := (cols.get (bridgeStageLayerIndex hcS s l)).2
               (((rw.ordPerm permG s (false, (l, r)) false + rw.ordPerm permG s (false, (l, r)) true : ℕ) : ℝ) / 2 +
                ((rw.ordPerm permG s (false, (l, (p l).symm r)) false + rw.ordPerm permG s (false, (l, (p l).symm r)) true : ℕ) : ℝ) / 2 +
                ((rw.ordPerm permG s (true, (l, gc_l.symm r)) false + rw.ordPerm permG s (true, (l, gc_l.symm r)) true : ℕ) : ℝ)))) -
             6 * rw.ordNongrowthAnchor s)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ (Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val),
            6 * rw.ordNongrowthHalfWidth s := by
          apply Finset.sum_le_sum; intro s hs_f
          have hs : rw.G ≤ s.val := (Finset.mem_filter.mp hs_f).2
          have h6A : 6 * rw.ordNongrowthAnchor s = ∑ _l : Fin 3, (2 * rw.ordNongrowthAnchor s) := by
            simp; ring
          have h6W : 6 * rw.ordNongrowthHalfWidth s = ∑ _l : Fin 3, (2 * rw.ordNongrowthHalfWidth s) := by
            simp; ring
          rw [h6A, h6W, ← Finset.sum_sub_distrib]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
          set gc_l := (cols.get (bridgeStageLayerIndex hcS s l)).2
          have hb1 := abs_le.mp (hnongrowth_pair s hs (false, (l, r)))
          have hb2 := abs_le.mp (hnongrowth_pair s hs (false, (l, (p l).symm r)))
          have hb3 := abs_le.mp (hnongrowth_pair s hs (true, (l, gc_l.symm r)))
          exact abs_le.mpr ⟨by linarith, by linarith⟩
      _ ≤ ∑ s : Fin rw.S, 6 * rw.ordNongrowthHalfWidth s :=
          Finset.sum_le_univ_sum_of_nonneg fun s => mul_nonneg (by norm_num) (rw.hnongrowth_width_nn s)
  have hM_rest_col_anchor : ∀ col : Fin n,
      ∃ rectTerm : ℝ, 0 ≤ rectTerm ∧ rectTerm ≤ 2 * X ∧
        |(M_rest_col col - (((n - 12 * rw.S - 2 : ℕ) : ℝ) * μ₀ + rectTerm +
            ∑ s ∈ (Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val),
              6 * rw.ordNongrowthAnchor s))| ≤
          ∑ s : Fin rw.S, 6 * rw.ordNongrowthHalfWidth s := by
    intro col
    have hrect_b := ut_col_rect_term_bounds rw.hs rw.choice a hμ₀_nn hμ₀_le_X col
    have hd1 : Disjoint (columnCells col ∩ reserved) (columnCells col ∩ LayerPacking.layersSupport rows) :=
      hdis_res_r.mono Finset.inter_subset_right Finset.inter_subset_right
    have hd2 : Disjoint ((columnCells col ∩ reserved) ∪ (columnCells col ∩ LayerPacking.layersSupport rows))
        (columnCells col ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
      rw [← Finset.inter_union_distrib_left]
      exact hdis_res_c.mono Finset.inter_subset_right Finset.inter_subset_right
    have hsplit_c : columnCells col ∩ full = (columnCells col ∩ reserved) ∪
        (columnCells col ∩ LayerPacking.layersSupport rows) ∪
        (columnCells col ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
      dsimp [full]; rw [Finset.inter_union_distrib_left, Finset.inter_union_distrib_left]
    have hcard_c_layers : (columnCells col ∩ LayerPacking.layersSupport rows).card = 6 * rw.S ∧
        (columnCells col ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols)).card = 6 * rw.S := by
      have heq1 : columnCells col ∩ LayerPacking.layersSupport rows =
          (LayerPacking.layersSupport rows).filter (fun z => z.2 = col) := by ext z; simp [and_comm]
      have heq2 : columnCells col ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols) =
          (LayerPacking.transposeCells (LayerPacking.layersSupport cols)).filter (fun z => z.2 = col) := by
        ext z; simp [and_comm]
      rw [heq1, heq2, (hcol_layer_cards col).1, (hcol_layer_cards col).2, hlen_p]
      exact ⟨by ring, by ring⟩
    have hsdiff_card : (columnCells col \ full).card = (n - 12 * rw.S - 2) + (2 - (columnCells col ∩ reserved).card) := by
      have htot_c := Finset.card_sdiff_add_card_inter (columnCells col) full
      have hcc_n : (columnCells col).card = n := by
        dsimp [columnCells]; rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)]; simp
      have hfull_c : (columnCells col ∩ full).card = (columnCells col ∩ reserved).card + 12 * rw.S := by
        rw [hsplit_c, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
          hcard_c_layers.1, hcard_c_layers.2]; ring
      have hq2 : (columnCells col ∩ reserved).card ≤ 2 := hrect_b.1
      have h12S : 12 * rw.S + 2 ≤ n := by have h := rw.hpack_ord; clear * - h; omega
      clear * - htot_c hcc_n hfull_c hq2 h12S; omega
    have hord_eq := ut_col_ord_midpoint_eq p rows cols hrS hcS hcmap hr hc a
      (rw.ordPerm permG) rw.ordGap (fun s l e => rw.ordPerm_pair permG s (true, (l, e)))
      hrow_a hcol_a (fun e => sumGap (true, e)) (fun _ => rfl) col
    let rectTerm := (∑ z ∈ columnCells col ∩ reserved, (entry a z : ℝ)) +
      ((2 - (columnCells col ∩ reserved).card : ℕ) : ℝ) * μ₀
    refine ⟨rectTerm, hrect_b.2.1, hrect_b.2.2, ?_⟩
    have hM_eq : M_rest_col col = ((n - 12 * rw.S - 2 : ℕ) : ℝ) * μ₀ + rectTerm +
        ∑ s ∈ (Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val),
          ∑ l : Fin 3,
            (let gr_l := (rows.get (bridgeStageLayerIndex hrS s l)).2
             (((rw.ordPerm permG s (false, (l, gr_l.symm col)) false + rw.ordPerm permG s (false, (l, gr_l.symm col)) true : ℕ) : ℝ) +
              ((rw.ordPerm permG s (true, (l, col)) false + rw.ordPerm permG s (true, (l, col)) true : ℕ) : ℝ) / 2 +
              ((rw.ordPerm permG s (true, (l, (p l).symm col)) false + rw.ordPerm permG s (true, (l, (p l).symm col)) true : ℕ) : ℝ) / 2)) := by
      dsimp [M_rest_col, M_col_ideal, R_div_col]
      rw [hsplit_c, Finset.sum_union hd2, Finset.sum_union hd1, hsdiff_card, Nat.cast_add]
      have hrearr : (∑ x ∈ columnCells col ∩ reserved, (entry a x : ℝ)) +
          (∑ x ∈ columnCells col ∩ LayerPacking.layersSupport rows, (entry a x : ℝ)) +
          (∑ x ∈ columnCells col ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols), (entry a x : ℝ)) +
          (((n - 12 * rw.S - 2 : ℕ) : ℝ) + ((2 - (columnCells col ∩ reserved).card : ℕ) : ℝ)) * μ₀ +
          (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
            (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (sumGap (true, e) : ℤ)) e col : ℝ) =
          ((n - 12 * rw.S - 2 : ℕ) : ℝ) * μ₀ + rectTerm +
          ((∑ x ∈ columnCells col ∩ LayerPacking.layersSupport rows, (entry a x : ℝ)) +
           (∑ x ∈ columnCells col ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols), (entry a x : ℝ)) +
           (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
             (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (sumGap (true, e) : ℤ)) e col : ℝ)) := by
        dsimp [rectTerm]; ring
      rw [hrearr, hord_eq, hS_split]
      have hg_eq : (∑ g : Fin rw.G, ∑ l : Fin 3,
          (((rw.ordPerm permG (gStage g) (false, (l, (gr (gStage g) l).symm col)) false + rw.ordPerm permG (gStage g) (false, (l, (gr (gStage g) l).symm col)) true : ℕ) : ℝ) +
           ((rw.ordPerm permG (gStage g) (true, (l, col)) false + rw.ordPerm permG (gStage g) (true, (l, col)) true : ℕ) : ℝ) / 2 +
           ((rw.ordPerm permG (gStage g) (true, (l, (p l).symm col)) false + rw.ordPerm permG (gStage g) (true, (l, (p l).symm col)) true : ℕ) : ℝ) / 2)) =
          growthLine (Sum.inr col) := by
        dsimp [growthLine]
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun g _ => hgrowth_col_stage col g
      rw [hg_eq]; dsimp [rectTerm]; ring
    rw [hM_eq]
    have hsub_eq : (((n - 12 * rw.S - 2 : ℕ) : ℝ) * μ₀ + rectTerm +
        ∑ s ∈ (Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val),
          ∑ l : Fin 3,
            (let gr_l := (rows.get (bridgeStageLayerIndex hrS s l)).2
             (((rw.ordPerm permG s (false, (l, gr_l.symm col)) false + rw.ordPerm permG s (false, (l, gr_l.symm col)) true : ℕ) : ℝ) +
              ((rw.ordPerm permG s (true, (l, col)) false + rw.ordPerm permG s (true, (l, col)) true : ℕ) : ℝ) / 2 +
              ((rw.ordPerm permG s (true, (l, (p l).symm col)) false + rw.ordPerm permG s (true, (l, (p l).symm col)) true : ℕ) : ℝ) / 2))) -
        (((n - 12 * rw.S - 2 : ℕ) : ℝ) * μ₀ + rectTerm +
          ∑ s ∈ (Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val),
            6 * rw.ordNongrowthAnchor s) =
        ∑ s ∈ (Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val),
          ((∑ l : Fin 3,
            (let gr_l := (rows.get (bridgeStageLayerIndex hrS s l)).2
             (((rw.ordPerm permG s (false, (l, gr_l.symm col)) false + rw.ordPerm permG s (false, (l, gr_l.symm col)) true : ℕ) : ℝ) +
              ((rw.ordPerm permG s (true, (l, col)) false + rw.ordPerm permG s (true, (l, col)) true : ℕ) : ℝ) / 2 +
              ((rw.ordPerm permG s (true, (l, (p l).symm col)) false + rw.ordPerm permG s (true, (l, (p l).symm col)) true : ℕ) : ℝ) / 2))) -
           6 * rw.ordNongrowthAnchor s) := by
      rw [Finset.sum_sub_distrib]; ring
    rw [hsub_eq]
    calc |∑ s ∈ (Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val),
          ((∑ l : Fin 3,
            (let gr_l := (rows.get (bridgeStageLayerIndex hrS s l)).2
             (((rw.ordPerm permG s (false, (l, gr_l.symm col)) false + rw.ordPerm permG s (false, (l, gr_l.symm col)) true : ℕ) : ℝ) +
              ((rw.ordPerm permG s (true, (l, col)) false + rw.ordPerm permG s (true, (l, col)) true : ℕ) : ℝ) / 2 +
              ((rw.ordPerm permG s (true, (l, (p l).symm col)) false + rw.ordPerm permG s (true, (l, (p l).symm col)) true : ℕ) : ℝ) / 2))) -
           6 * rw.ordNongrowthAnchor s)|
        ≤ ∑ s ∈ (Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val),
            |((∑ l : Fin 3,
              (let gr_l := (rows.get (bridgeStageLayerIndex hrS s l)).2
               (((rw.ordPerm permG s (false, (l, gr_l.symm col)) false + rw.ordPerm permG s (false, (l, gr_l.symm col)) true : ℕ) : ℝ) +
                ((rw.ordPerm permG s (true, (l, col)) false + rw.ordPerm permG s (true, (l, col)) true : ℕ) : ℝ) / 2 +
                ((rw.ordPerm permG s (true, (l, (p l).symm col)) false + rw.ordPerm permG s (true, (l, (p l).symm col)) true : ℕ) : ℝ) / 2))) -
             6 * rw.ordNongrowthAnchor s)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ (Finset.univ : Finset (Fin rw.S)).filter (fun s => rw.G ≤ s.val),
            6 * rw.ordNongrowthHalfWidth s := by
          apply Finset.sum_le_sum; intro s hs_f
          have hs : rw.G ≤ s.val := (Finset.mem_filter.mp hs_f).2
          have h6A : 6 * rw.ordNongrowthAnchor s = ∑ _l : Fin 3, (2 * rw.ordNongrowthAnchor s) := by
            simp; ring
          have h6W : 6 * rw.ordNongrowthHalfWidth s = ∑ _l : Fin 3, (2 * rw.ordNongrowthHalfWidth s) := by
            simp; ring
          rw [h6A, h6W, ← Finset.sum_sub_distrib]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
          set gr_l := (rows.get (bridgeStageLayerIndex hrS s l)).2
          have hb1 := abs_le.mp (hnongrowth_pair s hs (false, (l, gr_l.symm col)))
          have hb2 := abs_le.mp (hnongrowth_pair s hs (true, (l, col)))
          have hb3 := abs_le.mp (hnongrowth_pair s hs (true, (l, (p l).symm col)))
          exact abs_le.mpr ⟨by linarith, by linarith⟩
      _ ≤ ∑ s : Fin rw.S, 6 * rw.ordNongrowthHalfWidth s :=
          Finset.sum_le_univ_sum_of_nonneg fun s => mul_nonneg (by norm_num) (rw.hnongrowth_width_nn s)
  -- Non-growth width bound and mean distance of `M_rest_row`, `M_rest_col`
  have hW_ng_ub : (∑ s : Fin rw.S, 6 * rw.ordNongrowthHalfWidth s) ≤
      (60 / 1000 : ℝ) * X + (192 / 10000 : ℝ) * ((utWOrd n : ℝ) * X) := by
    have h1 := rw.hnongrowth_width_sum
    have h2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hH0Max_le_WOrd (by norm_num : (0 : ℝ) ≤ 72 / 10000)) hX_pos.le
    dsimp [X] at h1 h2 ⊢
    linarith [show ((60 / 1000 : ℝ) + (72 / 10000 : ℝ) * (utH0Max n : ℝ) + (12 / 1000 : ℝ) * (utWOrd n : ℝ)) * utX n =
      (60 / 1000 : ℝ) * utX n + (72 / 10000 : ℝ) * ((utH0Max n : ℝ) * utX n) + (12 / 1000 : ℝ) * ((utWOrd n : ℝ) * utX n) by ring]
  have hM_rest_row_dist : ∀ r : Fin n,
      |M_rest_row r - (y - K_growth)| ≤
        (2120 / 1000 : ℝ) * X + (384 / 10000 : ℝ) * ((utWOrd n : ℝ) * X) := by
    have hsum_rest : (∑ r : Fin n, M_rest_row r) = (n : ℝ) * (y - K_growth) := by
      dsimp [M_rest_row]; rw [Finset.sum_sub_distrib, hrow_ideal_sum, hgrowth_row_sum]; ring
    refine ut_mean_dist_le_pairwise_width hn_pos M_rest_row (y - K_growth) _ hsum_rest (fun r₁ r₂ => ?_)
    obtain ⟨rt₁, hrt1_lo, hrt1_hi, hb₁⟩ := hM_rest_row_anchor r₁
    obtain ⟨rt₂, hrt2_lo, hrt2_hi, hb₂⟩ := hM_rest_row_anchor r₂
    have hb₁' := abs_le.mp hb₁
    have hb₂' := abs_le.mp hb₂
    exact abs_le.mpr ⟨by linarith [hW_ng_ub], by linarith [hW_ng_ub]⟩
  have hM_rest_col_dist : ∀ col : Fin n,
      |M_rest_col col - (y - K_growth)| ≤
        (2120 / 1000 : ℝ) * X + (384 / 10000 : ℝ) * ((utWOrd n : ℝ) * X) := by
    have hsum_rest : (∑ col : Fin n, M_rest_col col) = (n : ℝ) * (y - K_growth) := by
      dsimp [M_rest_col]; rw [Finset.sum_sub_distrib, hcol_ideal_sum, hgrowth_col_sum]; ring
    refine ut_mean_dist_le_pairwise_width hn_pos M_rest_col (y - K_growth) _ hsum_rest (fun c₁ c₂ => ?_)
    obtain ⟨ct₁, hct1_lo, hct1_hi, hb₁⟩ := hM_rest_col_anchor c₁
    obtain ⟨ct₂, hct2_lo, hct2_hi, hb₂⟩ := hM_rest_col_anchor c₂
    have hb₁' := abs_le.mp hb₁
    have hb₂' := abs_le.mp hb₂
    exact abs_le.mpr ⟨by linarith [hW_ng_ub], by linarith [hW_ng_ub]⟩
  -- Reference centering error between `(rowSum c + R_div_row)` and `rowSum b₀`
  let δ_center (u : UTEdge n) : ℝ := (sumGap u : ℝ) / 2 - (evenGridCenter (rw.edgeRadius u) : ℝ)
  have hδ_center_bounds : ∀ u : UTEdge n,
      0 ≤ δ_center u ∧ δ_center u ≤ (6 / 10000 : ℝ) * ((utWOrd n : ℝ) * X) + 1 := by
    intro u
    have htot : (sumGap u : ℝ) = (rw.edgeA u : ℝ) + (rw.edgeRadius u : ℝ) := by
      dsimp [sumGap]; exact_mod_cast (rw.hedge_tot u).symm
    have hcent := evenGridCenter_midpoint_error (rw.edgeRadius u) (rw.hedge_even u)
    have hc_lo : 2 * (evenGridCenter (rw.edgeRadius u) : ℝ) ≤ (rw.edgeRadius u : ℝ) := by
      exact_mod_cast hcent.1
    have hc_hi : (rw.edgeRadius u : ℝ) ≤ 2 * (evenGridCenter (rw.edgeRadius u) : ℝ) + 2 := by
      exact_mod_cast (show rw.edgeRadius u ≤ 2 * evenGridCenter (rw.edgeRadius u) + 2 by
        clear * - hcent; omega)
    have hAub : (rw.edgeA u : ℝ) ≤ (12 / 10000 : ℝ) * ((utWOrd n : ℝ) * X) := by
      have h1 := rw.hedgeA_ub u
      have h2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hH0Max_le_WOrd (by norm_num : (0 : ℝ) ≤ 12 / 10000)) hX_pos.le
      dsimp [X] at h2 ⊢; linarith
    have hAnn : 0 ≤ (rw.edgeA u : ℝ) := Nat.cast_nonneg _
    dsimp [δ_center]; rw [htot]
    exact ⟨by linarith, by linarith⟩
  have hdiv_eval : ∀ (g : Fin 3 × Fin n → ℝ) (i : Fin n),
      (∑ e : Fin 3 × Fin n,
        ((if e.2 = i then g e else 0) - (if p e.1 e.2 = i then g e else 0))) =
      ∑ l : Fin 3, (g (l, i) - g (l, (p l).symm i)) := by
    intro g i
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    congr 1
    rw [← Equiv.sum_comp (p l).symm]
    simp only [Equiv.apply_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have het_cast : ∀ (f : Fin 3 × Fin n → ℕ) (e : Fin 3 × Fin n) (i : Fin n),
      (edgeTransfer Prod.snd (fun x : Fin 3 × Fin n => p x.1 x.2) (fun x => (f x : ℤ)) e i : ℝ) =
      (if e.2 = i then (f e : ℝ) else 0) - (if p e.1 e.2 = i then (f e : ℝ) else 0) := by
    intro f e i; unfold edgeTransfer; dsimp only; split_ifs <;> push_cast <;> ring
  have hX_lb_main : (283 / 100 : ℝ) * 10 ^ 10 ≤ X := by dsimp [X, utX]; linarith [hX_283]
  have hcenter_row_err : ∀ r : Fin n,
      |((rowSum c r : ℝ) + R_div_row r) - (rowSum b₀ r : ℝ)| ≤
        (1 / 1000 : ℝ) * X + (18 / 10000 : ℝ) * ((utWOrd n : ℝ) * X) := by
    intro r
    have hinv_R : (rowSum b₀ r : ℝ) - (rowSum c r : ℝ) =
        ∑ e : Fin 3 × Fin n,
          (edgeTransfer Prod.snd (fun x => p x.1 x.2)
            (fun x => (evenGridCenter (rw.edgeRadius (false, x)) : ℤ)) e r : ℝ) := by
      exact_mod_cast hrinvoice r
    have hdiff_eq : ((rowSum c r : ℝ) + R_div_row r) - (rowSum b₀ r : ℝ) =
        ∑ l : Fin 3, (δ_center (false, (l, r)) - δ_center (false, (l, (p l).symm r))) := by
      have h1 : R_div_row r = (1 / 2 : ℝ) * ∑ l : Fin 3,
          ((sumGap (false, (l, r)) : ℝ) - (sumGap (false, (l, (p l).symm r)) : ℝ)) := by
        dsimp [R_div_row]
        simp only [het_cast (fun e => sumGap (false, e))]
        rw [hdiv_eval]
      have h2 : (rowSum b₀ r : ℝ) - (rowSum c r : ℝ) = ∑ l : Fin 3,
          ((evenGridCenter (rw.edgeRadius (false, (l, r))) : ℝ) -
           (evenGridCenter (rw.edgeRadius (false, (l, (p l).symm r))) : ℝ)) := by
        rw [hinv_R]
        simp only [het_cast (fun e => evenGridCenter (rw.edgeRadius (false, e)))]
        rw [hdiv_eval]
      have h3 : (1 / 2 : ℝ) * (∑ l : Fin 3,
            ((sumGap (false, (l, r)) : ℝ) - (sumGap (false, (l, (p l).symm r)) : ℝ))) -
          (∑ l : Fin 3,
            ((evenGridCenter (rw.edgeRadius (false, (l, r))) : ℝ) -
             (evenGridCenter (rw.edgeRadius (false, (l, (p l).symm r))) : ℝ))) =
          ∑ l : Fin 3, (δ_center (false, (l, r)) - δ_center (false, (l, (p l).symm r))) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro l _; dsimp [δ_center]; ring
      linarith
    rw [hdiff_eq]
    have hsum_le : |∑ l : Fin 3, (δ_center (false, (l, r)) - δ_center (false, (l, (p l).symm r)))| ≤
        3 * ((6 / 10000 : ℝ) * ((utWOrd n : ℝ) * X) + 1) := by
      calc |∑ l : Fin 3, (δ_center (false, (l, r)) - δ_center (false, (l, (p l).symm r)))|
          ≤ ∑ l : Fin 3, |δ_center (false, (l, r)) - δ_center (false, (l, (p l).symm r))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _l : Fin 3, ((6 / 10000 : ℝ) * ((utWOrd n : ℝ) * X) + 1) := by
            apply Finset.sum_le_sum; intro l _
            have hb1 := hδ_center_bounds (false, (l, r))
            have hb2 := hδ_center_bounds (false, (l, (p l).symm r))
            exact abs_le.mpr ⟨by linarith, by linarith⟩
        _ = 3 * ((6 / 10000 : ℝ) * ((utWOrd n : ℝ) * X) + 1) := by simp [nsmul_eq_mul]; ring
    linarith [hX_lb_main]
  have hcenter_col_err : ∀ col : Fin n,
      |((columnSum c col : ℝ) + R_div_col col) - (columnSum b₀ col : ℝ)| ≤
        (1 / 1000 : ℝ) * X + (18 / 10000 : ℝ) * ((utWOrd n : ℝ) * X) := by
    intro col
    have hinv_C : (columnSum b₀ col : ℝ) - (columnSum c col : ℝ) =
        ∑ e : Fin 3 × Fin n,
          (edgeTransfer Prod.snd (fun x => p x.1 x.2)
            (fun x => (evenGridCenter (rw.edgeRadius (true, x)) : ℤ)) e col : ℝ) := by
      exact_mod_cast hcinvoice col
    have hdiff_eq : ((columnSum c col : ℝ) + R_div_col col) - (columnSum b₀ col : ℝ) =
        ∑ l : Fin 3, (δ_center (true, (l, col)) - δ_center (true, (l, (p l).symm col))) := by
      have h1 : R_div_col col = (1 / 2 : ℝ) * ∑ l : Fin 3,
          ((sumGap (true, (l, col)) : ℝ) - (sumGap (true, (l, (p l).symm col)) : ℝ)) := by
        dsimp [R_div_col]
        simp only [het_cast (fun e => sumGap (true, e))]
        rw [hdiv_eval]
      have h2 : (columnSum b₀ col : ℝ) - (columnSum c col : ℝ) = ∑ l : Fin 3,
          ((evenGridCenter (rw.edgeRadius (true, (l, col))) : ℝ) -
           (evenGridCenter (rw.edgeRadius (true, (l, (p l).symm col))) : ℝ)) := by
        rw [hinv_C]
        simp only [het_cast (fun e => evenGridCenter (rw.edgeRadius (true, e)))]
        rw [hdiv_eval]
      have h3 : (1 / 2 : ℝ) * (∑ l : Fin 3,
            ((sumGap (true, (l, col)) : ℝ) - (sumGap (true, (l, (p l).symm col)) : ℝ))) -
          (∑ l : Fin 3,
            ((evenGridCenter (rw.edgeRadius (true, (l, col))) : ℝ) -
             (evenGridCenter (rw.edgeRadius (true, (l, (p l).symm col))) : ℝ))) =
          ∑ l : Fin 3, (δ_center (true, (l, col)) - δ_center (true, (l, (p l).symm col))) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro l _; dsimp [δ_center]; ring
      linarith
    rw [hdiff_eq]
    have hsum_le : |∑ l : Fin 3, (δ_center (true, (l, col)) - δ_center (true, (l, (p l).symm col)))| ≤
        3 * ((6 / 10000 : ℝ) * ((utWOrd n : ℝ) * X) + 1) := by
      calc |∑ l : Fin 3, (δ_center (true, (l, col)) - δ_center (true, (l, (p l).symm col)))|
          ≤ ∑ l : Fin 3, |δ_center (true, (l, col)) - δ_center (true, (l, (p l).symm col))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _l : Fin 3, ((6 / 10000 : ℝ) * ((utWOrd n : ℝ) * X) + 1) := by
            apply Finset.sum_le_sum; intro l _
            have hb1 := hδ_center_bounds (true, (l, col))
            have hb2 := hδ_center_bounds (true, (l, (p l).symm col))
            exact abs_le.mpr ⟨by linarith, by linarith⟩
        _ = 3 * ((6 / 10000 : ℝ) * ((utWOrd n : ℝ) * X) + 1) := by simp [nsmul_eq_mul]; ring
    linarith [hX_lb_main]
  -- Step 8: Integer demand box, cut-capacity gate, and bounded integer flow realization (`b₀` -> `b`)
  let B_dem : ℕ := ⌈((5800 / 1000 : ℝ) + (170 / 1000 : ℝ) * (utWOrd n : ℝ)) * X⌉₊
  have hB_dem_ge : (5800 / 1000 : ℝ) * X + (170 / 1000 : ℝ) * ((utWOrd n : ℝ) * X) ≤ (B_dem : ℝ) := by
    have h : ((5800 / 1000 : ℝ) + (170 / 1000 : ℝ) * (utWOrd n : ℝ)) * X ≤ (B_dem : ℝ) :=
      Nat.le_ceil _
    linarith [show ((5800 / 1000 : ℝ) + (170 / 1000 : ℝ) * (utWOrd n : ℝ)) * X =
      (5800 / 1000 : ℝ) * X + (170 / 1000 : ℝ) * ((utWOrd n : ℝ) * X) by ring]
  have hB_dem_lt : (B_dem : ℝ) < (5800 / 1000 : ℝ) * X + (170 / 1000 : ℝ) * ((utWOrd n : ℝ) * X) + 1 := by
    have h : (B_dem : ℝ) < ((5800 / 1000 : ℝ) + (170 / 1000 : ℝ) * (utWOrd n : ℝ)) * X + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith [show ((5800 / 1000 : ℝ) + (170 / 1000 : ℝ) * (utWOrd n : ℝ)) * X =
      (5800 / 1000 : ℝ) * X + (170 / 1000 : ℝ) * ((utWOrd n : ℝ) * X) by ring]
  have hgr_bal_exp : ∀ line : Fin n ⊕ Fin n,
      |growthLine line - K_growth| ≤ (8192 / 1000 : ℝ) * X + (136 / 1000 : ℝ) * ((utWOrd n : ℝ) * X) := by
    intro line
    have hb := hgrowth_bal line
    linarith [show ((8192 / 1000 : ℝ) + (136 / 1000 : ℝ) * (utWOrd n : ℝ)) * X =
      (8192 / 1000 : ℝ) * X + (136 / 1000 : ℝ) * ((utWOrd n : ℝ) * X) by ring]
  have hbr_dem : ∀ r : Fin n, |(t_vec r : ℤ) - (rowSum b₀ r : ℤ)| ≤ (2 : ℤ) * B_dem := by
    intro r
    have ht_b := abs_le.mp (((ht_props r).2.2).trans hD_t75_ub)
    have hrest_b := abs_le.mp (hM_rest_row_dist r)
    have hgr_b := abs_le.mp (hgr_bal_exp (Sum.inl r))
    have hc_err : |((rowSum c r : ℝ) + R_div_row r) - M_row_ideal r| ≤ (1150 / 1000 : ℝ) * X := by
      have hr_c := (hrows_c r).le
      have heq_sub : ((rowSum c r : ℝ) + R_div_row r) - M_row_ideal r =
          (rowSum c r : ℝ) - ((∑ z ∈ rowCells r ∩ full, (entry a z : ℝ)) + ((rowCells r \ full).card : ℝ) * μ₀) := by
        dsimp [M_row_ideal]; ring
      rw [heq_sub]
      dsimp [X, μ₀] at hr_c ⊢; linarith
    have hc_b := abs_le.mp hc_err
    have hcent_b := abs_le.mp (hcenter_row_err r)
    have hid_M : M_row_ideal r = M_rest_row r + growthLine (Sum.inl r) := by dsimp [M_rest_row]; ring
    have hreal_b : |(t_vec r : ℝ) - (rowSum b₀ r : ℝ)| ≤ 2 * (B_dem : ℝ) := by
      rw [abs_le]
      exact ⟨by linarith [hid_M, hB_dem_ge, hX_pos, hWX_nn],
             by linarith [hid_M, hB_dem_ge, hX_pos, hWX_nn]⟩
    exact_mod_cast hreal_b
  have hbc_dem : ∀ col : Fin n, |(t_vec col : ℤ) - (columnSum b₀ col : ℤ)| ≤ (2 : ℤ) * B_dem := by
    intro col
    have ht_b := abs_le.mp (((ht_props col).2.2).trans hD_t75_ub)
    have hrest_b := abs_le.mp (hM_rest_col_dist col)
    have hgr_b := abs_le.mp (hgr_bal_exp (Sum.inr col))
    have hc_err : |((columnSum c col : ℝ) + R_div_col col) - M_col_ideal col| ≤ (1150 / 1000 : ℝ) * X := by
      have hc_c := (hcols_c col).le
      have heq_sub : ((columnSum c col : ℝ) + R_div_col col) - M_col_ideal col =
          (columnSum c col : ℝ) - ((∑ z ∈ columnCells col ∩ full, (entry a z : ℝ)) + ((columnCells col \ full).card : ℝ) * μ₀) := by
        dsimp [M_col_ideal]; ring
      rw [heq_sub]
      dsimp [X, μ₀] at hc_c ⊢; linarith
    have hc_b := abs_le.mp hc_err
    have hcent_b := abs_le.mp (hcenter_col_err col)
    have hid_M : M_col_ideal col = M_rest_col col + growthLine (Sum.inr col) := by dsimp [M_rest_col]; ring
    have hreal_b : |(t_vec col : ℝ) - (columnSum b₀ col : ℝ)| ≤ 2 * (B_dem : ℝ) := by
      rw [abs_le]
      exact ⟨by linarith [hid_M, hB_dem_ge, hX_pos, hWX_nn],
             by linarith [hid_M, hB_dem_ge, hX_pos, hWX_nn]⟩
    exact_mod_cast hreal_b
  have hN_ge_2000 : 2000 ≤ N_cap := by
    have hC1000 : (1000 : ℝ) ≤ (C_half : ℝ) := by
      have hm := mul_le_mul_of_nonneg_right hWOrd_ge_95 hX_pos.le
      linarith [hC_half_gt, hX_lb_main, hm]
    have hC_nat : 1000 ≤ C_half := by exact_mod_cast hC1000
    dsimp [N_cap]; clear * - hC_nat; omega
  have hcut_gate : 400000 * B_dem < 199 * 999 * N_cap := by
    have hWX : 95 * X ≤ (utWOrd n : ℝ) * X := mul_le_mul_of_nonneg_right hWOrd_ge_95 hX_pos.le
    have hN_cast : (N_cap : ℝ) = 2 * (C_half : ℝ) := by dsimp [N_cap]; push_cast; ring
    have hreal : (400000 : ℝ) * (B_dem : ℝ) < (199 * 999 : ℝ) * (N_cap : ℝ) := by
      rw [hN_cast]
      linarith [hB_dem_lt, hC_half_gt, hWX, hX_lb_main]
    exact_mod_cast hreal
  obtain ⟨hb₀_row_tot, hb₀_col_tot⟩ := ut_rowSum_and_columnSum_total b₀
  let dr : Fin n → ℤ := fun r => halfLineDemand (t_vec r) (rowSum b₀ r)
  let dc : Fin n → ℤ := fun col => halfLineDemand (t_vec col) (columnSum b₀ col)
  have ⟨hzr, her⟩ := halfLineDemand_system t_vec (rowSum b₀)
    (fun r => (ht_props r).2.1) (rowSum_odd hn_odd b₀) (ht_sum.trans hb₀_row_tot.symm)
  have ⟨hzc, hec⟩ := halfLineDemand_system t_vec (columnSum b₀)
    (fun col => (ht_props col).2.1) (columnSum_odd hn_odd b₀) (ht_sum.trans hb₀_col_tot.symm)
  have hdr_le : ∀ r, |dr r| ≤ (B_dem : ℤ) :=
    fun r => halfLineDemand_bound _ _ B_dem (ht_props r).2.1 (rowSum_odd hn_odd b₀ r) (hbr_dem r)
  have hdc_le : ∀ col, |dc col| ≤ (B_dem : ℤ) :=
    fun col => halfLineDemand_bound _ _ B_dem (ht_props col).2.1 (columnSum_odd hn_odd b₀ col) (hbc_dem col)
  have hcut_r := fc2k_cut_inequalities Prod.snd (fun e : Fin 3 × Fin n => p e.1 e.2)
    dr N_cap B_dem hN_ge_2000 hcut_gate hzr hdr_le hexp
  have hcut_c := fc2k_cut_inequalities Prod.snd (fun e : Fin 3 × Fin n => p e.1 e.2)
    dc N_cap B_dem hN_ge_2000 hcut_gate hzc hdc_le hexp
  obtain ⟨fr, hfr_b, hfr_div⟩ := integer_flow_of_cut_inequalities Prod.snd
    (fun e : Fin 3 × Fin n => p e.1 e.2) dr (N_cap / 2) hzr hcut_r
  obtain ⟨fc, hfc_b, hfc_div⟩ := integer_flow_of_cut_inequalities Prod.snd
    (fun e : Fin 3 × Fin n => p e.1 e.2) dc (N_cap / 2) hzc hcut_c
  obtain ⟨b, hrows_b, hcols_b, hmain_b, hanti_b, hfixed_b, _, _⟩ :=
    hflows fr (fun e => abs_le.mp (hfr_b e)) fc (fun e => abs_le.mp (hfc_b e))
  have hrow_prime_b : ∀ r, Nat.Prime (rowSum b r) := by
    intro r
    have h1 := hrows_b r
    rw [hfr_div r] at h1
    have h2 := her r
    have heq : rowSum b r = t_vec r := by
      exact_mod_cast (show (rowSum b r : ℤ) = t_vec r by dsimp [dr] at h1; linarith)
    rw [heq]; exact (ht_props r).1
  have hcol_prime_b : ∀ col, Nat.Prime (columnSum b col) := by
    intro col
    have h1 := hcols_b col
    rw [hfc_div col] at h1
    have h2 := hec col
    have heq : columnSum b col = t_vec col := by
      exact_mod_cast (show (columnSum b col : ℤ) = t_vec col by dsimp [dc] at h1; linarith)
    rw [heq]; exact (ht_props col).1
  -- Step 9: Diagonal interval overlap, common odd prime `p_diag`, and rectangle repair (`b` -> `result`)
  have hmain_inter : mainCells n ∩ full =
      (Finset.univ.filter (fun t : Fin rw.L => rw.choice t = true)).image
        (fun t => packedRectangleCorner rw.hs rw.choice (t, 0)) := by
    have h1 : mainCells n ∩ full = reserved ∩ mainCells n := by
      ext z; simp only [full, reserved, Finset.mem_inter, Finset.mem_union]
      have hr_off := fun hz => (hrowsafe z hz).2.1
      have hc_off := fun hz => (hcolsafe z hz).2.1
      tauto
    have h2 := active_rectangle_main_cells rw.hs rw.hL_ge3 rw.choice Finset.univ
    have hact : activeRectangleSupport rw.hs rw.choice Finset.univ = reserved :=
      ut_activeRectangleSupport_univ rw.hs rw.choice
    rw [hact] at h2
    exact h1.trans h2
  have hanti_inter : antiCells n ∩ full =
      (Finset.univ.filter (fun t : Fin rw.L => rw.choice t = false)).image
        (fun t => packedRectangleCorner rw.hs rw.choice (t, 0)) := by
    have h1 : antiCells n ∩ full = reserved ∩ antiCells n := by
      ext z; simp only [full, reserved, Finset.mem_inter, Finset.mem_union]
      have hr_off := fun hz => (hrowsafe z hz).2.2
      have hc_off := fun hz => (hcolsafe z hz).2.2
      tauto
    have h2 := active_rectangle_anti_cells rw.hs rw.hL_ge3 rw.choice Finset.univ
    have hact : activeRectangleSupport rw.hs rw.choice Finset.univ = reserved :=
      ut_activeRectangleSupport_univ rw.hs rw.choice
    rw [hact] at h2
    exact h1.trans h2
  have hcorner0_inj : Function.Injective (fun t : Fin rw.L => packedRectangleCorner rw.hs rw.choice (t, 0)) :=
    fun t₁ t₂ h => congrArg Prod.fst (packedRectangleCorner_injective rw.hs rw.choice h)
  have hm_sdiff_card : (mainCells n \ full).card = n - rw.L_half := by
    have hm_card : (mainCells n ∩ full).card = rw.L_half := by
      rw [hmain_inter, Finset.card_image_of_injective _ hcorner0_inj, rw.hchoice_true_card]
    have hms := Finset.card_sdiff_add_card_inter (mainCells n) full
    rw [hm_card, mainCells_card] at hms
    clear * - hms; omega
  have ha_sdiff_card : (antiCells n \ full).card = n - rw.L_half := by
    have ha_card : (antiCells n ∩ full).card = rw.L_half := by
      rw [hanti_inter, Finset.card_image_of_injective _ hcorner0_inj, rw.hchoice_false_card]
    have has := Finset.card_sdiff_add_card_inter (antiCells n) full
    rw [ha_card, antiCells_card] at has
    clear * - has; omega
  let M_m : ℝ := (mainSum c : ℝ) + ((rw.Am : ℝ) + (rw.Rm : ℝ)) / 2
  let M_a : ℝ := (antiSum c : ℝ) + ((rw.Aa : ℝ) + (rw.Ra : ℝ)) / 2
  have hdiag_mid_diff : |M_m - M_a| ≤
      (147 / 1000 : ℝ) * X + (3 / 1000 : ℝ) * ((utWDiag n : ℝ) * X) := by
    have hm_sum : (∑ z ∈ mainCells n ∩ full, (entry a z : ℝ)) + ((rw.Am : ℝ) + (rw.Rm : ℝ)) / 2 =
        ∑ i ∈ (Finset.univ : Finset (Fin rw.L)).filter (fun i => rw.choice i = true),
          (((rw.diagRect i).u1 : ℝ) + ((rw.diagRect i).gap : ℝ) / 2) := by
      have htot_R : (rw.Am : ℝ) + (rw.Rm : ℝ) =
          ∑ i ∈ (Finset.univ : Finset (Fin rw.L)).filter (fun i => rw.choice i = true), ((rw.diagRect i).gap : ℝ) := by
        exact_mod_cast rw.hm_tot
      rw [hmain_inter, Finset.sum_image (fun x _ y _ h => hcorner0_inj h), htot_R,
        Finset.sum_div, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      have hc0 : entry a (packedRectangleCorner rw.hs rw.choice (i, 0)) = (rw.diagRect i).u1 := hrect_a (i, 0)
      rw [hc0]
    have ha_sum : (∑ z ∈ antiCells n ∩ full, (entry a z : ℝ)) + ((rw.Aa : ℝ) + (rw.Ra : ℝ)) / 2 =
        ∑ i ∈ (Finset.univ : Finset (Fin rw.L)).filter (fun i => rw.choice i = false),
          (((rw.diagRect i).u1 : ℝ) + ((rw.diagRect i).gap : ℝ) / 2) := by
      have htot_R : (rw.Aa : ℝ) + (rw.Ra : ℝ) =
          ∑ i ∈ (Finset.univ : Finset (Fin rw.L)).filter (fun i => rw.choice i = false), ((rw.diagRect i).gap : ℝ) := by
        exact_mod_cast rw.ha_tot
      rw [hanti_inter, Finset.sum_image (fun x _ y _ h => hcorner0_inj h), htot_R,
        Finset.sum_div, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      have hc0 : entry a (packedRectangleCorner rw.hs rw.choice (i, 0)) = (rw.diagRect i).u1 := hrect_a (i, 0)
      rw [hc0]
    have hmc := abs_le.mp hmain_c
    have hac := abs_le.mp hanti_c
    have hbal := abs_le.mp rw.hdiag_mid_bal
    have hbal_ub : ((140 / 1000 : ℝ) + (6 / 10000 : ℝ) * (utH0Max n : ℝ)) * utX n ≤
        (140 / 1000 : ℝ) * utX n + (3 / 1000 : ℝ) * ((utWDiag n : ℝ) * utX n) := by
      have h := mul_le_mul_of_nonneg_right hH0Max_le_5WDiag (by dsimp [X] at hX_pos; exact hX_pos.le)
      linarith [show ((140 / 1000 : ℝ) + (6 / 10000 : ℝ) * (utH0Max n : ℝ)) * utX n =
        (140 / 1000 : ℝ) * utX n + (6 / 10000 : ℝ) * ((utH0Max n : ℝ) * utX n) by ring]
    rw [hm_sdiff_card] at hmc
    rw [ha_sdiff_card] at hac
    dsimp [M_m, M_a, X] at hmc hac hbal hX_pos ⊢
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  let lo_diag : ℝ := max (((mainSum c + rw.Am : ℕ) : ℝ)) (((antiSum c + rw.Aa : ℕ) : ℝ))
  let hi_diag : ℝ := min (((mainSum c + rw.Rm : ℕ) : ℝ)) (((antiSum c + rw.Ra : ℕ) : ℝ))
  have hdiag_overlap : (929 / 2000000 : ℝ) * ((n : ℝ) * X) ≤ hi_diag - lo_diag := by
    have hmid_b := abs_le.mp hdiag_mid_diff
    have hsp_m : (1467 / 1000 : ℝ) * X + (932 / 1000 : ℝ) * ((utWDiag n : ℝ) * X) ≤
        (rw.Rm : ℝ) - (rw.Am : ℝ) := by
      have h := rw.hm_span; dsimp [X] at h ⊢
      linarith [show (1467 / 1000 + (932 / 1000 : ℝ) * (utWDiag n : ℝ)) * utX n =
        (1467 / 1000 : ℝ) * utX n + (932 / 1000 : ℝ) * ((utWDiag n : ℝ) * utX n) by ring]
    have hsp_a : (1467 / 1000 : ℝ) * X + (932 / 1000 : ℝ) * ((utWDiag n : ℝ) * X) ≤
        (rw.Ra : ℝ) - (rw.Aa : ℝ) := by
      have h := rw.ha_span; dsimp [X] at h ⊢
      linarith [show (1467 / 1000 + (932 / 1000 : ℝ) * (utWDiag n : ℝ)) * utX n =
        (1467 / 1000 : ℝ) * utX n + (932 / 1000 : ℝ) * ((utWDiag n : ℝ) * utX n) by ring]
    have hWD_X : (929 / 2000000 : ℝ) * ((n : ℝ) * X) ≤ (929 / 1000 : ℝ) * ((utWDiag n : ℝ) * X) := by
      have h := mul_le_mul_of_nonneg_right hWDiag_lin_lo hX_pos.le
      linarith
    have hlo_m : (((mainSum c + rw.Am : ℕ) : ℝ)) = M_m - ((rw.Rm : ℝ) - (rw.Am : ℝ)) / 2 := by
      dsimp [M_m]; push_cast; ring
    have hhi_m : (((mainSum c + rw.Rm : ℕ) : ℝ)) = M_m + ((rw.Rm : ℝ) - (rw.Am : ℝ)) / 2 := by
      dsimp [M_m]; push_cast; ring
    have hlo_a : (((antiSum c + rw.Aa : ℕ) : ℝ)) = M_a - ((rw.Ra : ℝ) - (rw.Aa : ℝ)) / 2 := by
      dsimp [M_a]; push_cast; ring
    have hhi_a : (((antiSum c + rw.Ra : ℕ) : ℝ)) = M_a + ((rw.Ra : ℝ) - (rw.Aa : ℝ)) / 2 := by
      dsimp [M_a]; push_cast; ring
    have h4 : lo_diag ≤ hi_diag - (929 / 2000000 : ℝ) * ((n : ℝ) * X) := by
      dsimp [lo_diag, hi_diag]
      refine max_le_iff.mpr ⟨le_sub_iff_add_le.mpr (le_min_iff.mpr ⟨?_, ?_⟩),
        le_sub_iff_add_le.mpr (le_min_iff.mpr ⟨?_, ?_⟩)⟩
      · rw [hlo_m, hhi_m]; linarith
      · rw [hlo_m, hhi_a]; linarith
      · rw [hlo_a, hhi_m]; linarith
      · rw [hlo_a, hhi_a]; linarith
    linarith
  have hlo_diag_ge : (5 * 10 ^ 10 : ℝ) ≤ lo_diag := by
    have hcard_half : (1 / 2 : ℝ) * (n : ℝ) ≤ ((n - rw.L_half : ℕ) : ℝ) := by
      have hnat : n ≤ 2 * (n - rw.L_half) := by
        have h1 := rw.hs; have h2 := rw.hL_def; clear * - h1 h2; omega
      have hreal : (n : ℝ) ≤ 2 * ((n - rw.L_half : ℕ) : ℝ) := by exact_mod_cast hnat
      linarith
    have hmc_lo := (abs_le.mp hmain_c).1
    rw [hm_sdiff_card] at hmc_lo
    have hsum_nn : 0 ≤ ∑ z ∈ mainCells n ∩ full, (entry a z : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hprod_lo : (1 / 2 : ℝ) * (35735 : ℝ) * ((3566 / 10000 : ℝ) * X) ≤
        ((n - rw.L_half : ℕ) : ℝ) * μ₀ := by
      have h1 : (1 / 2 : ℝ) * (35735 : ℝ) ≤ ((n - rw.L_half : ℕ) : ℝ) := by linarith [hnR, hcard_half]
      exact mul_le_mul h1 hμ₀_bounds.1 (by positivity) (Nat.cast_nonneg _)
    have hm_le_lo : (mainSum c : ℝ) ≤ lo_diag := by
      have h1 : (mainSum c : ℝ) ≤ (((mainSum c + rw.Am : ℕ) : ℝ)) := by
        exact_mod_cast Nat.le_add_right (mainSum c) rw.Am
      exact h1.trans (le_max_left _ _)
    dsimp [X, μ₀] at hmc_lo hprod_lo hX_lb_main
    linarith
  have hlo_diag_ub : lo_diag ≤ 2 * ((n : ℝ) * X) := by
    obtain ⟨hm_ub, ha_ub⟩ := ut_mainSum_and_antiSum_le_n_mul_poolMaximum c
    have hgap_ub : ∀ i : Fin rw.L, (rw.diagRect i).gap ≤ poolMaximum n := by
      intro i
      have hv1_pool : (rw.diagRect i).v1 ∈ pool n := rw.hV_sub _ (rw.hdiag_mem i 1)
      have hv1_le : (rw.diagRect i).v1 ≤ poolMaximum n := pool_le_poolMaximum hv1_pool
      have hv1_eq := (rw.diagRect i).hv1
      clear * - hv1_le hv1_eq; omega
    have hL_half_le_n : rw.L_half ≤ n := by
      have h1 := rw.hs; have h2 := rw.hL_def; clear * - h1 h2; omega
    have hAm_ub : (rw.Am : ℝ) ≤ (n : ℝ) * X := by
      have h2Am : 2 * rw.Am ≤ n * poolMaximum n := by
        calc 2 * rw.Am ≤ rw.Am + rw.Rm := by have h := rw.hAm_le_Rm; clear * - h; omega
          _ = ∑ i ∈ (Finset.univ : Finset (Fin rw.L)).filter (fun i => rw.choice i = true), (rw.diagRect i).gap := rw.hm_tot
          _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin rw.L)).filter (fun i => rw.choice i = true), poolMaximum n :=
              Finset.sum_le_sum fun i _ => hgap_ub i
          _ = rw.L_half * poolMaximum n := by rw [Finset.sum_const, smul_eq_mul, rw.hchoice_true_card]
          _ ≤ n * poolMaximum n := Nat.mul_le_mul_right _ hL_half_le_n
      have hAm_le : rw.Am ≤ n * poolMaximum n := by clear * - h2Am; omega
      dsimp [X, utX]
      exact_mod_cast hAm_le
    have hAa_ub : (rw.Aa : ℝ) ≤ (n : ℝ) * X := by
      have h2Aa : 2 * rw.Aa ≤ n * poolMaximum n := by
        calc 2 * rw.Aa ≤ rw.Aa + rw.Ra := by have h := rw.hAa_le_Ra; clear * - h; omega
          _ = ∑ i ∈ (Finset.univ : Finset (Fin rw.L)).filter (fun i => rw.choice i = false), (rw.diagRect i).gap := rw.ha_tot
          _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin rw.L)).filter (fun i => rw.choice i = false), poolMaximum n :=
              Finset.sum_le_sum fun i _ => hgap_ub i
          _ = rw.L_half * poolMaximum n := by rw [Finset.sum_const, smul_eq_mul, rw.hchoice_false_card]
          _ ≤ n * poolMaximum n := Nat.mul_le_mul_right _ hL_half_le_n
      have hAa_le : rw.Aa ≤ n * poolMaximum n := by clear * - h2Aa; omega
      dsimp [X, utX]
      exact_mod_cast hAa_le
    have hm_ub_R : (mainSum c : ℝ) ≤ (n : ℝ) * X := by dsimp [X, utX]; exact_mod_cast hm_ub
    have ha_ub_R : (antiSum c : ℝ) ≤ (n : ℝ) * X := by dsimp [X, utX]; exact_mod_cast ha_ub
    dsimp [lo_diag]
    refine max_le_iff.mpr ⟨?_, ?_⟩
    · have h1 : (((mainSum c + rw.Am : ℕ) : ℝ)) = (mainSum c : ℝ) + (rw.Am : ℝ) := Nat.cast_add _ _
      linarith
    · have h1 : (((antiSum c + rw.Aa : ℕ) : ℝ)) = (antiSum c : ℝ) + (rw.Aa : ℝ) := Nat.cast_add _ _
      linarith
  let hi_win : ℝ := (9000 / 8999 : ℝ) * lo_diag
  have hhi_win_le : hi_win ≤ hi_diag := by
    have hnX_nn : 0 ≤ (n : ℝ) * X := by positivity
    dsimp [hi_win]; linarith [hlo_diag_ub, hdiag_overlap]
  obtain ⟨p_diag, hp_prime, hp_odd, hp_gt_lo, hp_le_win⟩ :=
    odd_prime_in_interval_all_scales bmor imp (lo := lo_diag) (hi := hi_win)
      hlo_diag_ge (by dsimp [hi_win]; linarith) (by dsimp [hi_win]; linarith)
  have hp_le_hi : (p_diag : ℝ) ≤ hi_diag := hp_le_win.trans hhi_win_le
  have hreachm : (rw.Am : ℤ) ≤ (p_diag : ℤ) - mainSum c ∧ (p_diag : ℤ) - mainSum c ≤ rw.Rm := by
    have hlo_m : (((mainSum c + rw.Am : ℕ) : ℝ)) ≤ (p_diag : ℝ) := (le_max_left _ _).trans hp_gt_lo.le
    have hhi_m : (p_diag : ℝ) ≤ (((mainSum c + rw.Rm : ℕ) : ℝ)) := hp_le_hi.trans (min_le_left _ _)
    have h1 : mainSum c + rw.Am ≤ p_diag := by exact_mod_cast hlo_m
    have h2 : p_diag ≤ mainSum c + rw.Rm := by exact_mod_cast hhi_m
    clear * - h1 h2; omega
  have hreacha : (rw.Aa : ℤ) ≤ (p_diag : ℤ) - antiSum c ∧ (p_diag : ℤ) - antiSum c ≤ rw.Ra := by
    have hlo_a : (((antiSum c + rw.Aa : ℕ) : ℝ)) ≤ (p_diag : ℝ) := (le_max_right _ _).trans hp_gt_lo.le
    have hhi_a : (p_diag : ℝ) ≤ (((antiSum c + rw.Ra : ℕ) : ℝ)) := hp_le_hi.trans (min_le_right _ _)
    have h1 : antiSum c + rw.Aa ≤ p_diag := by exact_mod_cast hlo_a
    have h2 : p_diag ≤ antiSum c + rw.Ra := by exact_mod_cast hhi_a
    clear * - h1 h2; omega
  have hrect_c : ∀ x : Fin rw.L × Fin 4,
      entry c (packedRectangleCorner rw.hs rw.choice x) = (rw.diagRect x.1).corners x.2 := by
    intro x
    have hmem : packedRectangleCorner rw.hs rw.choice x ∈ full :=
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩))
    exact (hfixed_c _ hmem).trans (hrect_a x)
  have hgaps_c : ∀ i ∈ (Finset.univ : Finset (Fin rw.L)),
      entry c (RectanglePacking.firstRow rw.hs i, RectanglePacking.secondColumn rw.hs rw.choice i) =
        entry c (RectanglePacking.firstRow rw.hs i, RectanglePacking.firstColumn rw.hs rw.choice i) + (rw.diagRect i).gap ∧
      entry c (RectanglePacking.secondRow rw.hs i, RectanglePacking.firstColumn rw.hs rw.choice i) =
        entry c (RectanglePacking.secondRow rw.hs i, RectanglePacking.secondColumn rw.hs rw.choice i) + (rw.diagRect i).gap := by
    intro i _
    have h0 := hrect_c (i, 0)
    have h1 := hrect_c (i, 1)
    have h2 := hrect_c (i, 2)
    have h3 := hrect_c (i, 3)
    dsimp [packedRectangleCorner, UTRectData.corners] at h0 h1 h2 h3
    rw [h1, h0, h2, h3]
    exact ⟨(rw.diagRect i).hv1, (rw.diagRect i).hv2⟩
  have hagree_bc : ∀ z ∈ packedLabelSupport rw.hs rw.choice Finset.univ, entry b z = entry c z := by
    intro z hz
    have hres : z ∈ reserved := ut_packedLabelSupport_univ_subset rw.hs rw.choice hz
    exact (hfixed_b z hres).trans (hfixed₀ z hres)
  obtain ⟨result, _, _, _, _, hvalid, _, _, _⟩ :=
    packed_prime_diagonal_repair_of_evenIntervalGrid rw.hs rw.hL_ge3 hn_odd rw.choice
      (fun i => (rw.diagRect i).gap) Finset.univ rw.Am rw.Rm rw.Aa rw.Ra c b ∅
      rw.hm_grid rw.ha_grid
      hgaps_c (fun _ h => Finset.notMem_empty _ h |>.elim) hagree_bc
      (hmain_b.trans hm₀) (hanti_b.trans ha₀) hrow_prime_b hcol_prime_b
      p_diag hp_prime hp_odd hreachm hreacha
  exact ⟨result, hvalid⟩

end

end Sude


