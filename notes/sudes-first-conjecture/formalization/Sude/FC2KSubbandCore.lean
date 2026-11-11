import Sude.FC2KJointInstallation
import Sude.FC2KT75AnalyticSupply
import Sude.FC2KBridgeAndDiagonalHelpers
import Sude.FWPhysicalRadiusCentering
import Sude.TargetRouting
import Sude.PackedReachablePrimeDiagonal

/-!
# FC2K Sub-Band Routing & Diagonal Repair Core (`FC2KSubbandCore`)

Completes the proof of `HasSquare n` across `2001 ≤ n ≤ 19483, Odd n` from an
`FC2KCompletedWitness` (and directly from `GeneralPrefixProfile` + scalar sub-band gates via
`fc2k_subband_hasSquare`):
1. Selects prime row/column target vectors `t_vec` via `fc2k_t75_targets_low` (`n ≤ 9299`)
   or `fc2k_t75_targets_high` (`9301 ≤ n`).
2. Centers both ordinary networks (`b₀`) and bounds `|(rowSum b₀ r : ℝ) - y|` and
   `|(columnSum b₀ col : ℝ) - y|` via `M_row_ideal`, `M_col_ideal`, and `fw_reference_invoice_radius_bounds`.
3. Routes exact integer flows via `fc2k_cut_inequalities` + `integer_flow_of_cut_inequalities` +
   `twoNetworks_realize_bounded_integer_flows_with_invoice`, obtaining `b` with prime row and column sums.
4. Selects an odd prime `p_diag` in the reachable diagonal overlap via `odd_prime_in_interval_all_scales`
   and repairs both diagonals simultaneously via `packed_prime_diagonal_repair_reachable_target`.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- If `g : Fin n → ℝ` has mean `y` and pairwise differences `≤ W`, every `|g i - y| ≤ W`. -/
theorem mean_dist_le_pairwise_width {n : ℕ} (hn : 0 < n) (g : Fin n → ℝ) (y W : ℝ)
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

/-- Full `packedLabelSupport` on `Finset.univ` is contained in `packedRectangleSupport`. -/
theorem packedLabelSupport_univ_subset_packedRectangleSupport {L n : ℕ}
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

/-- Both full diagonal sums of any square `b : Cell n ≃ Fin (n * n)` are bounded by `n * poolMaximum n`. -/
theorem mainSum_and_antiSum_le_n_mul_poolMaximum {n : ℕ} (b : Cell n ≃ Fin (n * n)) :
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

/-- Exact row-sum and column-sum totals of any square `b : Cell n ≃ Fin (n * n)`. -/
theorem rowSum_and_columnSum_total {n : ℕ} (b : Cell n ≃ Fin (n * n)) :
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

/-- Route prime row and column targets and repair both diagonals to a common prime from an
`FC2KCompletedWitness`. -/
theorem fc2k_hasSquare_of_completed_witness
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports) (rs : RSPrimeCountImports)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    {n P qCert corrLo maxHi J_max W_ord W_diag N_bins : ℕ} {δ ε μ_lo μ_hi : ℝ}
    {prof : GeneralPrefixProfile P qCert corrLo maxHi}
    {roles : FC2KSelectedRoles n P qCert corrLo maxHi J_max W_ord W_diag N_bins δ prof}
    (w : FC2KCompletedWitness n P qCert corrLo maxHi J_max W_ord W_diag N_bins δ ε μ_lo μ_hi prof roles)
    (hn : 2001 ≤ n) (hnmax : n ≤ 19483) (hodd : Odd n)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    {N_cap B_dem : ℕ}
    (hN_min : 2000 ≤ N_cap)
    (hN_rad : 2 * (N_cap : ℝ) ≤
      (poolMaximum n : ℝ) + (W_ord : ℝ) *
        (2 * fc2kPoolMean n - ((1 / 250 : ℝ) + 2 * (N_bins : ℝ) * δ) * (poolMaximum n : ℝ)))
    (hB_cap : 400000 * B_dem < 199 * 999 * N_cap)
    (hB_dem :
      let X : ℝ := poolMaximum n
      let m : ℝ := fc2kPoolMean n
      let D_t75 : ℝ := if n ≤ 9299 then (23 / 50 : ℝ) * X else ((n : ℝ) * m) / 400
      let loB_ext := min (min (2 * (corrLo : ℝ)) (min ((197 / 200 : ℝ) * X) (2 * m - δ * X))) (2 * μ_lo)
      let hiB_ext := max (max (2 * (maxHi : ℝ)) (max ((203 / 200 : ℝ) * X) (2 * m + δ * X))) (2 * μ_hi)
      D_t75 + ((hiB_ext - loB_ext) + ((2 * prof.totalSpanWords * 49152 : ℕ) : ℝ) +
        (9 / 50 : ℝ) * (J_max : ℝ) * X + 12 * (W_ord : ℝ) * δ * X) +
        (1 + 10 * ε) * X + 9 / 2 ≤ 2 * (B_dem : ℝ))
    (hdiag_lo : (5 * 10 ^ 10 : ℝ) ≤
      ((n - (12 * P + 12 * J_max + W_diag) : ℕ) : ℝ) * μ_lo - 2 * ε * (poolMaximum n : ℝ))
    (hdiag_2X : 2 * (poolMaximum n : ℝ) ≤
      ((n - (12 * P + 12 * J_max + W_diag) : ℕ) : ℝ) * μ_lo - 2 * ε * (poolMaximum n : ℝ))
    (hdiag_overlap :
      let X : ℝ := poolMaximum n
      let m : ℝ := fc2kPoolMean n
      2 * X + ((prof.totalSpanWords * 49152 : ℕ) : ℝ) +
        (9 / 25 : ℝ) * (J_max : ℝ) * X + (W_diag : ℝ) * δ * X +
        (401 / 100 : ℝ) * ε * X + 2 ≤
      12 * X + (W_diag : ℝ) * (2 * m - ((1 / 250 : ℝ) + 2 * (N_bins : ℝ) * δ) * X)) :
    HasSquare n := by
  let X : ℝ := poolMaximum n
  let m : ℝ := fc2kPoolMean n
  let y : ℝ := (n : ℝ) * m
  have hn_pos : 0 < n := by omega
  have hX_pos : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hJ_le : (roles.J : ℝ) ≤ (J_max : ℝ) := Nat.cast_le.mpr roles.hJ_le
  -- Step 1: Select T75 prime target vector `t_vec`
  let D_t75 : ℝ := if n ≤ 9299 then (23 / 50 : ℝ) * X else y / 400
  have ht_exists : ∃ f : Fin n → ℕ,
      (∑ i, f i) = Lucas.poolTotal n ∧
      (∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ) - y| ≤ D_t75) := by
    have hy_eq : (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue = y := by
      rw [prescribedPoolValues_mean]; rfl
    by_cases hn9299 : n ≤ 9299
    · obtain ⟨f, hsum, hf⟩ := fc2k_t75_targets_low bmor rs sharp upperSharp hn hn9299 hodd
      refine ⟨f, hsum, fun i => ?_⟩
      dsimp [D_t75]; rw [if_pos hn9299, ← hy_eq]; exact hf i
    · have hn9301 : 9301 ≤ n := by obtain ⟨k, hk⟩ := hodd; omega
      obtain ⟨f, hsum, hf⟩ := fc2k_t75_targets_high imp rs sharp upperSharp hn9301 hnmax hodd
      refine ⟨f, hsum, fun i => ?_⟩
      dsimp [D_t75]; rw [if_neg hn9299, ← hy_eq]; exact hf i
  obtain ⟨t_vec, ht_sum, ht_props⟩ := ht_exists
  -- Step 2: Bound `|w.M_row_ideal r - y|` and `|w.M_col_ideal col - y|`
  have hpool_eq_ny : (Lucas.poolTotal n : ℝ) = (n : ℝ) * y := by
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn_pos)
    dsimp [y, m, fc2kPoolMean]
    push_cast
    field_simp
  let loB_ext := min (min (2 * (corrLo : ℝ)) (min ((197 / 200 : ℝ) * X) (2 * m - δ * X))) (2 * μ_lo)
  let hiB_ext := max (max (2 * (maxHi : ℝ)) (max ((203 / 200 : ℝ) * X) (2 * m + δ * X))) (2 * μ_hi)
  let W_max := (hiB_ext - loB_ext) + ((2 * prof.totalSpanWords * 49152 : ℕ) : ℝ) +
    (9 / 50 : ℝ) * (J_max : ℝ) * X + 12 * (W_ord : ℝ) * δ * X
  have hlo_ext_le : loB_ext ≤
      min (min (2 * (corrLo : ℝ)) (min ((197 / 200 : ℝ) * X) (2 * m - δ * X))) (2 * w.μ₀) :=
    min_le_min le_rfl (by linarith [w.hμ₀_bounds.1])
  have hhi_ext_ge :
      max (max (2 * (maxHi : ℝ)) (max ((203 / 200 : ℝ) * X) (2 * m + δ * X))) (2 * w.μ₀) ≤ hiB_ext :=
    max_le_max le_rfl (by linarith [w.hμ₀_bounds.2])
  have hrow_y : ∀ r : Fin n, |w.M_row_ideal r - y| ≤ W_max := by
    apply mean_dist_le_pairwise_width hn_pos w.M_row_ideal y W_max
      (w.hrow_ideal_sum.trans hpool_eq_ny)
    intro r₁ r₂
    have hw := w.hrow_ideal_width r₁ r₂
    dsimp only at hw
    have hJ_mul : (9 / 50 : ℝ) * (roles.J : ℝ) * X ≤ (9 / 50 : ℝ) * (J_max : ℝ) * X := by nlinarith
    dsimp [W_max]; linarith [hw, hlo_ext_le, hhi_ext_ge, hJ_mul]
  have hcol_y : ∀ col : Fin n, |w.M_col_ideal col - y| ≤ W_max := by
    apply mean_dist_le_pairwise_width hn_pos w.M_col_ideal y W_max
      (w.hcol_ideal_sum.trans hpool_eq_ny)
    intro c₁ c₂
    have hw := w.hcol_ideal_width c₁ c₂
    dsimp only at hw
    have hJ_mul : (9 / 50 : ℝ) * (roles.J : ℝ) * X ≤ (9 / 50 : ℝ) * (J_max : ℝ) * X := by nlinarith
    dsimp [W_max]; linarith [hw, hlo_ext_le, hhi_ext_ge, hJ_mul]
  -- Step 3: Center networks (`b₀`) and route prime row/column targets (`b`)
  have hR_cap : ∀ e, 2 * N_cap ≤ w.BR.radius e := by
    intro e
    rw [w.hR_rad e]
    have hlow := roles.hedge_lower e
    exact_mod_cast (le_trans hN_rad hlow)
  have hC_cap : ∀ e, 2 * N_cap ≤ w.BC.radius e := by
    intro e
    rw [w.hC_rad e]
    have hlow := roles.hedge_lower e
    exact_mod_cast (le_trans hN_rad hlow)
  let reserved := packedRectangleSupport w.hs w.choice
  obtain ⟨b₀, hinvoice, hm₀, ha₀, hfixed₀, hflows⟩ :=
    twoNetworks_realize_bounded_integer_flows_with_invoice w.c reserved w.rows w.cols
      w.hr w.hc w.rowGap w.colGap w.hrowGap_c w.hcolGap_c w.BR w.BC N_cap hR_cap hC_cap
  obtain ⟨hr_inv_bound, hc_inv_bound⟩ :=
    fw_reference_invoice_radius_bounds w.p w.c b₀ reserved w.rows w.cols
      w.hr w.hc w.rowGap w.colGap w.hrowGap_c w.hcolGap_c w.BR w.BC w.hends hinvoice
  have hbr_dem : ∀ r : Fin n, |(t_vec r : ℤ) - rowSum b₀ r| ≤ (2 : ℤ) * B_dem := by
    intro r
    have hinv_r : |(rowSum b₀ r : ℝ) - ((rowSum w.c r : ℝ) +
        (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
          (edgeTransfer Prod.snd (fun e => w.p e.1 e.2) (fun e => (w.BR.radius e : ℤ)) e r : ℝ))| ≤ 9 / 2 := by
      have hz : |(2 * (rowSum b₀ r : ℤ) - (2 * (rowSum w.c r : ℤ) +
          ∑ e : Fin 3 × Fin n, edgeTransfer Prod.snd (fun e => w.p e.1 e.2)
            (fun e => (w.BR.radius e : ℤ)) e r) : ℝ)| ≤ 9 := by
        exact_mod_cast hr_inv_bound r
      have h1 := abs_le.mp hz
      push_cast at h1
      rw [abs_le]
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have hc_r := le_of_lt (w.hrow_c_approx r)
    have hy_r := hrow_y r
    have ht_r := (ht_props r).2.2
    have hreal_bound : |(t_vec r : ℝ) - (rowSum b₀ r : ℝ)| ≤ 2 * (B_dem : ℝ) := by
      have ha1 := abs_le.mp ht_r
      have ha2 := abs_le.mp hy_r
      have ha3 := abs_le.mp hc_r
      have ha4 := abs_le.mp hinv_r
      have hB : D_t75 + W_max + (1 + 10 * ε) * X + 9 / 2 ≤ 2 * (B_dem : ℝ) := hB_dem
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    have hcast : |(t_vec r : ℝ) - (rowSum b₀ r : ℝ)| ≤ ((2 * B_dem : ℤ) : ℝ) := by
      push_cast; exact hreal_bound
    exact_mod_cast hcast
  have hbc_dem : ∀ col : Fin n, |(t_vec col : ℤ) - columnSum b₀ col| ≤ (2 : ℤ) * B_dem := by
    intro col
    have hinv_c : |(columnSum b₀ col : ℝ) - ((columnSum w.c col : ℝ) +
        (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
          (edgeTransfer Prod.snd (fun e => w.p e.1 e.2) (fun e => (w.BC.radius e : ℤ)) e col : ℝ))| ≤ 9 / 2 := by
      have hz : |(2 * (columnSum b₀ col : ℤ) - (2 * (columnSum w.c col : ℤ) +
          ∑ e : Fin 3 × Fin n, edgeTransfer Prod.snd (fun e => w.p e.1 e.2)
            (fun e => (w.BC.radius e : ℤ)) e col) : ℝ)| ≤ 9 := by
        exact_mod_cast hc_inv_bound col
      have h1 := abs_le.mp hz
      push_cast at h1
      rw [abs_le]
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have hc_c := le_of_lt (w.hcol_c_approx col)
    have hy_c := hcol_y col
    have ht_c := (ht_props col).2.2
    have hreal_bound : |(t_vec col : ℝ) - (columnSum b₀ col : ℝ)| ≤ 2 * (B_dem : ℝ) := by
      have ha1 := abs_le.mp ht_c
      have ha2 := abs_le.mp hy_c
      have ha3 := abs_le.mp hc_c
      have ha4 := abs_le.mp hinv_c
      have hB : D_t75 + W_max + (1 + 10 * ε) * X + 9 / 2 ≤ 2 * (B_dem : ℝ) := hB_dem
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    have hcast : |(t_vec col : ℝ) - (columnSum b₀ col : ℝ)| ≤ ((2 * B_dem : ℤ) : ℝ) := by
      push_cast; exact hreal_bound
    exact_mod_cast hcast
  obtain ⟨hb₀_row_tot, hb₀_col_tot⟩ := rowSum_and_columnSum_total b₀
  let dr : Fin n → ℤ := fun r => halfLineDemand (t_vec r) (rowSum b₀ r)
  let dc : Fin n → ℤ := fun col => halfLineDemand (t_vec col) (columnSum b₀ col)
  obtain ⟨hzr, her⟩ := halfLineDemand_system t_vec (rowSum b₀)
    (fun r => (ht_props r).2.1) (rowSum_odd hodd b₀) (ht_sum.trans hb₀_row_tot.symm)
  obtain ⟨hzc, hec⟩ := halfLineDemand_system t_vec (columnSum b₀)
    (fun col => (ht_props col).2.1) (columnSum_odd hodd b₀) (ht_sum.trans hb₀_col_tot.symm)
  have hdr_le : ∀ r, |dr r| ≤ (B_dem : ℤ) :=
    fun r => halfLineDemand_bound _ _ B_dem (ht_props r).2.1 (rowSum_odd hodd b₀ r) (hbr_dem r)
  have hdc_le : ∀ col, |dc col| ≤ (B_dem : ℤ) :=
    fun col => halfLineDemand_bound _ _ B_dem (ht_props col).2.1 (columnSum_odd hodd b₀ col) (hbc_dem col)
  have hexp_R : ∀ S : Finset (Fin n), 199 * min S.card (n - S.card) ≤
      200 * (cutEdges w.BR.source w.BR.target S).card := by
    have hs_eq : w.BR.source = Prod.snd := funext (fun e => (w.hends e).1)
    have ht_eq : w.BR.target = fun e => w.p e.1 e.2 := funext (fun e => (w.hends e).2.2.1)
    rw [hs_eq, ht_eq]; exact w.hexp
  have hexp_C : ∀ S : Finset (Fin n), 199 * min S.card (n - S.card) ≤
      200 * (cutEdges w.BC.source w.BC.target S).card := by
    have hs_eq : w.BC.source = Prod.snd := funext (fun e => (w.hends e).2.1)
    have ht_eq : w.BC.target = fun e => w.p e.1 e.2 := funext (fun e => (w.hends e).2.2.2)
    rw [hs_eq, ht_eq]; exact w.hexp
  obtain ⟨fr, hfr, hdivr⟩ := integer_flow_of_cut_inequalities w.BR.source w.BR.target dr (N_cap / 2)
    hzr (fc2k_cut_inequalities w.BR.source w.BR.target dr N_cap B_dem hN_min hB_cap hzr hdr_le hexp_R)
  obtain ⟨fc, hfc, hdivc⟩ := integer_flow_of_cut_inequalities w.BC.source w.BC.target dc (N_cap / 2)
    hzc (fc2k_cut_inequalities w.BC.source w.BC.target dc N_cap B_dem hN_min hB_cap hzc hdc_le hexp_C)
  obtain ⟨b, hrows_b, hcols_b, hm_b, ha_b, hfixed_b, _, _⟩ :=
    hflows fr (fun e => abs_le.mp (hfr e)) fc (fun e => abs_le.mp (hfc e))
  have hrow_prime : ∀ r : Fin n, Nat.Prime (rowSum b r) := by
    intro r
    have h1 := hrows_b r
    rw [hdivr r] at h1
    dsimp only [dr] at h1
    have h2 := her r
    have heq : rowSum b r = t_vec r := by exact_mod_cast (show (rowSum b r : ℤ) = t_vec r by omega)
    rw [heq]; exact (ht_props r).1
  have hcol_prime : ∀ col : Fin n, Nat.Prime (columnSum b col) := by
    intro col
    have h1 := hcols_b col
    rw [hdivc col] at h1
    dsimp only [dc] at h1
    have h2 := hec col
    have heq : columnSum b col = t_vec col := by exact_mod_cast (show (columnSum b col : ℤ) = t_vec col by omega)
    rw [heq]; exact (ht_props col).1
  have hm_bc : mainSum b = mainSum w.c := hm_b.trans hm₀
  have ha_bc : antiSum b = antiSum w.c := ha_b.trans ha₀
  -- Step 4: Select odd prime `p_diag` in reachable diagonal overlap and repair both diagonals
  have heven_Rm : 2 ∣ roles.Rm := by
    rw [roles.hRm_sum]; exact Finset.dvd_sum (fun t _ => (roles.hrect_gap t).2.1)
  have heven_Ra : 2 ∣ roles.Ra := by
    rw [roles.hRa_sum]; exact Finset.dvd_sum (fun t _ => (roles.hrect_gap t).2.1)
  have hcent_Rm := evenGridCenter_midpoint_error roles.Rm heven_Rm
  have hcent_Ra := evenGridCenter_midpoint_error roles.Ra heven_Ra
  have hcent_Rm_R : (roles.Rm : ℝ) - 2 ≤ 2 * (evenGridCenter roles.Rm : ℝ) := by
    have h2 : roles.Rm ≤ 2 * evenGridCenter roles.Rm + 2 := by omega
    have h2R : (roles.Rm : ℝ) ≤ 2 * (evenGridCenter roles.Rm : ℝ) + 2 := by exact_mod_cast h2
    linarith
  have hcent_Ra_R : (roles.Ra : ℝ) - 2 ≤ 2 * (evenGridCenter roles.Ra : ℝ) := by
    have h2 : roles.Ra ≤ 2 * evenGridCenter roles.Ra + 2 := by omega
    have h2R : (roles.Ra : ℝ) ≤ 2 * (evenGridCenter roles.Ra : ℝ) + 2 := by exact_mod_cast h2
    linarith
  let lo_diag : ℝ := max (mainSum w.c : ℝ) (antiSum w.c : ℝ)
  let hi_diag : ℝ := min ((mainSum w.c : ℝ) + 2 * (evenGridCenter roles.Rm : ℝ))
    ((antiSum w.c : ℝ) + 2 * (evenGridCenter roles.Ra : ℝ))
  let hi_win : ℝ := lo_diag + 2 * X
  have hwin_le_diag : hi_win ≤ hi_diag := by
    let D_err : ℝ := ((prof.totalSpanWords * 49152 : ℕ) : ℝ) +
      (9 / 25 : ℝ) * (J_max : ℝ) * X + (W_diag : ℝ) * δ * X + (401 / 100 : ℝ) * ε * X
    let minR : ℝ := 12 * X + (W_diag : ℝ) * (2 * m - ((1 / 250 : ℝ) + 2 * (N_bins : ℝ) * δ) * X)
    have hD_nn : 0 ≤ D_err := by dsimp [D_err]; positivity
    have hJ_mul2 : (9 / 25 : ℝ) * (roles.J : ℝ) * X ≤ (9 / 25 : ℝ) * (J_max : ℝ) * X := by nlinarith
    have hmd := abs_le.mp w.hmain_diff_c
    have hmd1 : -D_err ≤ (mainSum w.c : ℝ) + (roles.Rm : ℝ) / 2 - ((antiSum w.c : ℝ) + (roles.Ra : ℝ) / 2) := by
      dsimp [D_err]; linarith [hmd.1, hJ_mul2]
    have hmd2 : (mainSum w.c : ℝ) + (roles.Rm : ℝ) / 2 - ((antiSum w.c : ℝ) + (roles.Ra : ℝ) / 2) ≤ D_err := by
      dsimp [D_err]; linarith [hmd.2, hJ_mul2]
    have hRm_lo : minR ≤ (roles.Rm : ℝ) := roles.hRm_lower
    have hRa_lo : minR ≤ (roles.Ra : ℝ) := roles.hRa_lower
    have hov : 2 * X + D_err + 2 ≤ minR := by
      dsimp only at hdiag_overlap
      dsimp [D_err, minR]
      linarith [hdiag_overlap]
    dsimp [hi_win, hi_diag, lo_diag]
    rw [← max_add_add_right]
    exact le_min (max_le (by linarith) (by linarith)) (max_le (by linarith) (by linarith))
  have hlo_5e10 : (5 * 10 ^ 10 : ℝ) ≤ lo_diag :=
    le_trans hdiag_lo (le_trans w.hmain_lo_c (le_max_left _ _))
  have hlo_2X : 2 * X ≤ lo_diag :=
    le_trans hdiag_2X (le_trans w.hmain_lo_c (le_max_left _ _))
  have hlo_ub : lo_diag ≤ 19483 * X := by
    obtain ⟨hm_ub, ha_ub⟩ := mainSum_and_antiSum_le_n_mul_poolMaximum w.c
    have hnX : (n : ℝ) * X ≤ 19483 * X :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hnmax) hX_pos.le
    exact max_le (hm_ub.trans hnX) (ha_ub.trans hnX)
  obtain ⟨p_diag, hp_prime, hp_odd, hp_gt_lo, hp_le_win⟩ :=
    odd_prime_in_interval_all_scales bmor imp (hi := hi_win) hlo_5e10 (by linarith) (by linarith)
  have hp_le_diag : (p_diag : ℝ) ≤ hi_diag := hp_le_win.trans hwin_le_diag
  have hreachm : 0 ≤ ((p_diag : ℤ) - mainSum w.c) ∧
      (p_diag : ℤ) - mainSum w.c ≤ 2 * evenGridCenter roles.Rm := by
    have h1R : (mainSum w.c : ℝ) ≤ (p_diag : ℝ) := le_trans (le_max_left _ _) (le_of_lt hp_gt_lo)
    have h2R : (p_diag : ℝ) ≤ (mainSum w.c : ℝ) + 2 * (evenGridCenter roles.Rm : ℝ) :=
      hp_le_diag.trans (min_le_left _ _)
    have h1N : mainSum w.c ≤ p_diag := by exact_mod_cast h1R
    have h2N : p_diag ≤ mainSum w.c + 2 * evenGridCenter roles.Rm := by exact_mod_cast h2R
    omega
  have hreacha : 0 ≤ ((p_diag : ℤ) - antiSum w.c) ∧
      (p_diag : ℤ) - antiSum w.c ≤ 2 * evenGridCenter roles.Ra := by
    have h1R : (antiSum w.c : ℝ) ≤ (p_diag : ℝ) := le_trans (le_max_right _ _) (le_of_lt hp_gt_lo)
    have h2R : (p_diag : ℝ) ≤ (antiSum w.c : ℝ) + 2 * (evenGridCenter roles.Ra : ℝ) :=
      hp_le_diag.trans (min_le_right _ _)
    have h1N : antiSum w.c ≤ p_diag := by exact_mod_cast h1R
    have h2N : p_diag ≤ antiSum w.c + 2 * evenGridCenter roles.Ra := by exact_mod_cast h2R
    omega
  let gapL : Fin w.L → ℕ := fun i => roles.rectGap (Fin.cast w.hL_def i)
  have hgrid_rel : ∀ (flag : Bool) (R_tot : ℕ),
      CompleteEvenGrid
        (Finset.univ.filter (fun t : Fin (24 * P + 24 * roles.J + 2 * W_diag) => decide (t.val % 2 = 0) = flag))
        roles.rectGap R_tot →
      CompleteEvenGrid
        ((Finset.univ : Finset (Fin w.L)).filter (fun i => w.choice i = flag))
        gapL R_tot := by
    intro flag R_tot hgrid
    let srcSet := Finset.univ.filter
      (fun t : Fin (24 * P + 24 * roles.J + 2 * W_diag) => decide (t.val % 2 = 0) = flag)
    let fSub : {x // x ∈ srcSet} → Fin w.L := fun x => Fin.cast w.hL_def.symm x.1
    have hfSub_inj : Function.Injective fSub := by
      rintro ⟨x₁, _⟩ ⟨x₂, _⟩ h
      exact Subtype.ext (Fin.cast_injective w.hL_def.symm h)
    have hrel := completeEvenGrid_finite_relabel srcSet roles.rectGap R_tot fSub hfSub_inj gapL
      (by rintro ⟨x, _⟩; simp [fSub, gapL]) hgrid
    have hset_eq : srcSet.attach.image fSub =
        (Finset.univ : Finset (Fin w.L)).filter (fun i => w.choice i = flag) := by
      ext i
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, srcSet,
        Finset.mem_filter, Finset.mem_univ, fSub, w.hchoice, fc2kDiagChoice]
      exact ⟨fun ⟨x, hx, hxi⟩ => by rw [← hxi]; simpa using hx,
        fun hi => ⟨Fin.cast w.hL_def i, by simpa using hi, by simp⟩⟩
    rw [hset_eq] at hrel
    exact hrel
  have hm_gridL := hgrid_rel true roles.Rm roles.hm_grid
  have ha_gridL := hgrid_rel false roles.Ra roles.ha_grid
  have hgaps : ∀ i ∈ (Finset.univ : Finset (Fin w.L)),
      entry w.c (RectanglePacking.firstRow w.hs i, RectanglePacking.secondColumn w.hs w.choice i) =
        entry w.c (RectanglePacking.firstRow w.hs i, RectanglePacking.firstColumn w.hs w.choice i) + gapL i ∧
      entry w.c (RectanglePacking.secondRow w.hs i, RectanglePacking.firstColumn w.hs w.choice i) =
        entry w.c (RectanglePacking.secondRow w.hs i, RectanglePacking.secondColumn w.hs w.choice i) + gapL i := by
    intro i _
    have hc0 : entry w.c (RectanglePacking.firstRow w.hs i, RectanglePacking.firstColumn w.hs w.choice i) =
        (roles.rectVal (Fin.cast w.hL_def i, 0)).val := w.hrect_c (i, 0)
    have hc1 : entry w.c (RectanglePacking.firstRow w.hs i, RectanglePacking.secondColumn w.hs w.choice i) =
        (roles.rectVal (Fin.cast w.hL_def i, 1)).val := w.hrect_c (i, 1)
    have hc2 : entry w.c (RectanglePacking.secondRow w.hs i, RectanglePacking.firstColumn w.hs w.choice i) =
        (roles.rectVal (Fin.cast w.hL_def i, 2)).val := w.hrect_c (i, 2)
    have hc3 : entry w.c (RectanglePacking.secondRow w.hs i, RectanglePacking.secondColumn w.hs w.choice i) =
        (roles.rectVal (Fin.cast w.hL_def i, 3)).val := w.hrect_c (i, 3)
    have hg := roles.hrect_gap (Fin.cast w.hL_def i)
    rw [hc0, hc1, hc2, hc3]
    exact ⟨hg.2.2.1, hg.2.2.2⟩
  have hagree : ∀ z ∈ packedLabelSupport w.hs w.choice Finset.univ, entry b z = entry w.c z := by
    intro z hz
    have hres := packedLabelSupport_univ_subset_packedRectangleSupport w.hs w.choice hz
    exact (hfixed_b z hres).trans (hfixed₀ z hres)
  obtain ⟨_, _, _, _, result, _, _, _, _, hvalid, _, _, _, _⟩ :=
    packed_prime_diagonal_repair_reachable_target w.hs w.hL hodd w.choice gapL Finset.univ
      roles.Rm roles.Ra w.c b ∅ hm_gridL ha_gridL hgaps (by simp) hagree hm_bc ha_bc
      hrow_prime hcol_prime (fun _ => p_diag) ⟨0, hn_pos⟩ hp_prime hp_odd hreachm hreacha
  exact ⟨result, hvalid⟩

/-- Unified FC2K sub-band closure theorem: given a verified `GeneralPrefixProfile` and scalar
Bridge / Wide / Central / Routing / Diagonal gates at `n ∈ [2001, 19483]`, Odd `n`,
concludes `HasSquare n`. -/
theorem fc2k_subband_hasSquare
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports) (rs : RSPrimeCountImports)
    (upper : RSIndexUpper) (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    {n P qCert corrLo maxHi J_max W_ord W_diag N_bins W_bin P_half P_full N_cap B_dem : ℕ}
    {δ ε μ_lo μ_hi : ℝ}
    (prof : GeneralPrefixProfile P qCert corrLo maxHi)
    (hn : 2001 ≤ n) (hnmax : n ≤ 19483) (hodd : Odd n) (hP : 1 ≤ P)
    (hq : 6 * (n + 8) ≤ qCert) (hmaxHi : maxHi ≤ poolMaximum n)
    (hδ : 0 < δ) (hε : 0 < ε)
    -- Bridge gates
    (hJ_cover : (poolMaximum n : ℝ) ≤
      bridgeIteration (poolMaximum n) ((2 ^ (P + 1) - 2 : ℕ) : ℝ) J_max)
    (M_br : ℕ → ℕ)
    (hbr_budget : ∀ (V_pref : Finset ℕ),
      V_pref ⊆ Finset.univ.image prof.values →
      V_pref.card = 12 * P * (n + 8) →
      ∀ j < J_max,
        bridgeIteration (poolMaximum n) ((2 ^ (P + 1) - 2 : ℕ) : ℝ) j < poolMaximum n →
        bridgeGeometricStageBudget n V_pref
          (bridgeIteration (poolMaximum n) ((2 ^ (P + 1) - 2 : ℕ) : ℝ)) (M_br j) (24 + 3 * n) j)
    -- Wide gates
    (hsep_mid : ((1 / 250 : ℝ) + 2 * (N_bins : ℝ) * δ) * (poolMaximum n : ℝ) ≤ 2 * fc2kPoolMean n)
    (hm_hi : 2 * fc2kPoolMean n < (poolMaximum n : ℝ))
    (hW_bin : ∀ z : Fin N_bins × Bool, (W_bin : ℝ) ≤
      ((fc2kWideRight (fc2kPoolMean n) (poolMaximum n) δ z -
        fc2kWideLeft (fc2kPoolMean n) (poolMaximum n) δ z) -
       (518 / 125 : ℝ) *
        (Real.sqrt (fc2kWideLeft (fc2kPoolMean n) (poolMaximum n) δ z) +
         Real.sqrt (fc2kWideRight (fc2kPoolMean n) (poolMaximum n) δ z))) /
        Real.log (poolMaximum n : ℝ))
    (hwide_gate : (N_bins : ℝ) * (poolMaximum n : ℝ) <
      ((N_bins * W_bin - 2 * (2 * W_diag + W_ord * (3 * n)) : ℕ) : ℝ) ^ 2)
    (hpref_lo_wide : ((1 / 500 : ℝ) + (N_bins : ℝ) * δ) * (poolMaximum n : ℝ) < (corrLo : ℝ))
    (hpref_hi_wide : (maxHi : ℝ) ≤
      2 * fc2kPoolMean n - ((1 / 500 : ℝ) + (N_bins : ℝ) * δ) * (poolMaximum n : ℝ))
    (hbr_lo_wide : ((1 / 500 : ℝ) + (N_bins : ℝ) * δ) * (poolMaximum n : ℝ) < (poolMaximum n : ℝ) / 4)
    (hbr_hi_wide : 3 * (poolMaximum n : ℝ) / 4 ≤
      2 * fc2kPoolMean n - ((1 / 500 : ℝ) + (N_bins : ℝ) * δ) * (poolMaximum n : ℝ))
    -- Packing & central completion gates
    (hs_max : 2 * (24 * P + 24 * J_max + 2 * W_diag) + 1 ≤ n)
    (hload_max : 4 * (12 * (P + J_max + W_ord) + 4) + 8 < n)
    (hres_max : 4 * (12 * P * (n + 8) + 12 * J_max * (n + 8) + 8 * W_diag + 12 * W_ord * n) ≤ n * n)
    (hμ_bounds : ∀ J ≤ J_max,
      let N_rem : ℝ := ((n * n - (12 * P * (n + 8) + 12 * J * (n + 8) + 8 * W_diag + 12 * W_ord * n) : ℕ) : ℝ)
      let S_lo : ℝ := 12 * (P : ℝ) * ((n : ℝ) + 8) * (corrLo : ℝ) +
        6 * (J : ℝ) * ((n : ℝ) + 8) * ((197 / 200 : ℝ) * (poolMaximum n : ℝ)) +
        (2 * (W_diag : ℝ) + (W_ord : ℝ) * (3 * (n : ℝ))) *
          (4 * fc2kPoolMean n - 2 * δ * (poolMaximum n : ℝ))
      let S_hi : ℝ := 12 * (P : ℝ) * ((n : ℝ) + 8) * (maxHi : ℝ) +
        6 * (J : ℝ) * ((n : ℝ) + 8) * ((203 / 200 : ℝ) * (poolMaximum n : ℝ)) +
        (2 * (W_diag : ℝ) + (W_ord : ℝ) * (3 * (n : ℝ))) *
          (4 * fc2kPoolMean n + 2 * δ * (poolMaximum n : ℝ))
      μ_lo * N_rem ≤ (Lucas.poolTotal n : ℝ) - S_hi ∧
      (Lucas.poolTotal n : ℝ) - S_lo ≤ μ_hi * N_rem)
    (hwide_sep_cent :
      let X : ℝ := poolMaximum n
      let δ_sh : ℝ := 6 * (ε * X) / ((n * n - 1 : ℕ) : ℝ)
      ((1 / 500 : ℝ) + (N_bins : ℝ) * δ) * X ≤ μ_lo - ε * X - δ_sh ∧
      μ_hi + ε * X + δ_sh ≤ 2 * fc2kPoolMean n - ((1 / 500 : ℝ) + (N_bins : ℝ) * δ) * X)
    (hcent_in_pool :
      let X : ℝ := poolMaximum n
      let δ_sh : ℝ := 6 * (ε * X) / ((n * n - 1 : ℕ) : ℝ)
      1 ≤ μ_lo - ε * X - δ_sh ∧ μ_hi + ε * X + δ_sh ≤ X)
    (hP_half : ∀ (V_pref : Finset ℕ),
      V_pref ⊆ Finset.univ.image prof.values →
      ∀ lo hi : ℝ,
        μ_lo - ε * (poolMaximum n : ℝ) ≤ lo →
        hi ≤ μ_hi + ε * (poolMaximum n : ℝ) →
        lo ≤ hi →
        hi - lo ≤ (ε / 2) * (poolMaximum n : ℝ) →
        (V_pref ∩ apInterval lo hi 2 1).card ≤ P_half)
    (hP_full : ∀ (V_pref : Finset ℕ),
      V_pref ⊆ Finset.univ.image prof.values →
      ∀ lo hi : ℝ,
        let X : ℝ := poolMaximum n
        let δ_sh : ℝ := 6 * (ε * X) / ((n * n - 1 : ℕ) : ℝ)
        μ_lo - ε * X - δ_sh ≤ lo →
        hi ≤ μ_hi + ε * X + δ_sh →
        lo ≤ hi →
        hi - lo ≤ 2 * ε * X + 2 * δ_sh →
        (V_pref ∩ apInterval lo hi 2 1).card ≤ P_full)
    (hhalf_gate :
      let X : ℝ := poolMaximum n
      ((2 * n - 1 : ℕ) : ℝ) ≤
        ((ε / 2) * X - (1036 / 125 : ℝ) * Real.sqrt X) / Real.log X -
          ((4 * J_max * (24 + 3 * n) + P_half : ℕ) : ℝ))
    (hfull_gate :
      let X : ℝ := poolMaximum n
      ((3 * n + 1 : ℕ) : ℝ) ≤
        (2 * (ε * X) - (1036 / 125 : ℝ) * Real.sqrt X) / Real.log X -
          ((4 * J_max * (24 + 3 * n) + P_full + (2 * n - 1) : ℕ) : ℝ))
    -- Routing & diagonal overlap gates
    (hN_min : 2000 ≤ N_cap)
    (hN_rad : 2 * (N_cap : ℝ) ≤
      (poolMaximum n : ℝ) + (W_ord : ℝ) *
        (2 * fc2kPoolMean n - ((1 / 250 : ℝ) + 2 * (N_bins : ℝ) * δ) * (poolMaximum n : ℝ)))
    (hB_cap : 400000 * B_dem < 199 * 999 * N_cap)
    (hB_dem :
      let X : ℝ := poolMaximum n
      let m : ℝ := fc2kPoolMean n
      let D_t75 : ℝ := if n ≤ 9299 then (23 / 50 : ℝ) * X else ((n : ℝ) * m) / 400
      let loB_ext := min (min (2 * (corrLo : ℝ)) (min ((197 / 200 : ℝ) * X) (2 * m - δ * X))) (2 * μ_lo)
      let hiB_ext := max (max (2 * (maxHi : ℝ)) (max ((203 / 200 : ℝ) * X) (2 * m + δ * X))) (2 * μ_hi)
      D_t75 + ((hiB_ext - loB_ext) + ((2 * prof.totalSpanWords * 49152 : ℕ) : ℝ) +
        (9 / 50 : ℝ) * (J_max : ℝ) * X + 12 * (W_ord : ℝ) * δ * X) +
        (1 + 10 * ε) * X + 9 / 2 ≤ 2 * (B_dem : ℝ))
    (hdiag_lo : (5 * 10 ^ 10 : ℝ) ≤
      ((n - (12 * P + 12 * J_max + W_diag) : ℕ) : ℝ) * μ_lo - 2 * ε * (poolMaximum n : ℝ))
    (hdiag_2X : 2 * (poolMaximum n : ℝ) ≤
      ((n - (12 * P + 12 * J_max + W_diag) : ℕ) : ℝ) * μ_lo - 2 * ε * (poolMaximum n : ℝ))
    (hdiag_overlap :
      let X : ℝ := poolMaximum n
      let m : ℝ := fc2kPoolMean n
      2 * X + ((prof.totalSpanWords * 49152 : ℕ) : ℝ) +
        (9 / 25 : ℝ) * (J_max : ℝ) * X + (W_diag : ℝ) * δ * X +
        (401 / 100 : ℝ) * ε * X + 2 ≤
      12 * X + (W_diag : ℝ) * (2 * m - ((1 / 250 : ℝ) + 2 * (N_bins : ℝ) * δ) * X)) :
    HasSquare n := by
  let poolProf := generalPrefixProfile_poolValues prof hmaxHi
  have hpoolProf_inj : Function.Injective poolProf :=
    generalPrefixProfile_poolValues_injective prof hmaxHi
  let prefValues := truncatePrefixValues hq poolProf
  have hpref_inj : Function.Injective prefValues :=
    truncatePrefixValues_injective hq poolProf hpoolProf_inj
  let V_pref0 : Finset ℕ := Finset.univ.image (fun x => (prefValues x).val)
  have hV0_sub : V_pref0 ⊆ Finset.univ.image prof.values := by
    intro v hv
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
    exact truncatePrefixValues_mem_full hq poolProf x
  have hV0_card : V_pref0.card = 12 * P * (n + 8) := by
    have hc := truncatePrefixValues_card hq poolProf hpoolProf_inj
    change V_pref0.card = 2 * (6 * (n + 8)) * P at hc
    rw [hc]; ring
  obtain ⟨roles⟩ := fc2k_select_roles bmor upper prof hn hnmax hP hq hmaxHi
    hJ_cover M_br (hbr_budget V_pref0 hV0_sub hV0_card)
    hδ hsep_mid hm_hi hW_bin hwide_gate hpref_lo_wide hpref_hi_wide hbr_lo_wide hbr_hi_wide
  obtain ⟨w⟩ := fc2k_joint_install_and_complete bmor upper roles hn hnmax hodd hP hε
    hs_max hload_max hres_max hμ_bounds hwide_sep_cent hcent_in_pool
    (hP_half roles.V_pref roles.hV_pref_sub) (hP_full roles.V_pref roles.hV_pref_sub)
    hhalf_gate hfull_gate
  exact fc2k_hasSquare_of_completed_witness bmor imp rs sharp upperSharp w hn hnmax hodd
    hδ.le hε.le hN_min hN_rad hB_cap hB_dem hdiag_lo hdiag_2X hdiag_overlap

end

end Sude
