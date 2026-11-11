import Sude.FWThetaFreshSpareOutputGrids
import Sude.FWFirstBandActiveDiagonalBound
import Sude.PackedReachablePrimeDiagonal
import Sude.APInterval
import Sude.FWT75NominalThetaDomain

/-! Reachable diagonal overlap subinterval and square completion for the first FW band. -/
namespace Sude
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Every entry of a physical square is at most `poolMaximum n`. -/
theorem physical_entry_le_poolMaximum {n : ℕ} (a : Cell n ≃ Fin (n * n)) (z : Cell n) :
    entry a z ≤ poolMaximum n := by
  exact_mod_cast (physical_entry_pool_range a z).2

/-- Both physical diagonal sums are at most `n * poolMaximum n`. -/
theorem physical_diagonal_sum_le {n : ℕ} (a : Cell n ≃ Fin (n * n)) :
    mainSum a ≤ n * poolMaximum n ∧ antiSum a ≤ n * poolMaximum n := by
  constructor
  · calc
      mainSum a = ∑ i : Fin n, entry a (i, i) := rfl
      _ ≤ ∑ _i : Fin n, poolMaximum n := Finset.sum_le_sum (fun i _ => physical_entry_le_poolMaximum a (i, i))
      _ = n * poolMaximum n := by simp
  · calc
      antiSum a = ∑ i : Fin n, entry a (i, i.rev) := rfl
      _ ≤ ∑ _i : Fin n, poolMaximum n := Finset.sum_le_sum (fun i _ => physical_entry_le_poolMaximum a (i, i.rev))
      _ = n * poolMaximum n := by simp

/-- Sharp lower bound on `poolMaximum n` in the first FW band (`n ≥ 19485`). -/
theorem fw_poolMaximum_gt_seven_billion (lower : RSIndexLower) {n : ℕ}
    (hnlo : 19485 ≤ n) : 7365505384 < poolMaximum n := by
  have hn' : (19485 : ℝ) ≤ n := by exact_mod_cast hnlo
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hj : (379665226 : ℝ) ≤ j := by
    dsimp [j]
    push_cast
    nlinarith
  have hthreshold : (2 : ℝ) ^ 28 ≤ j := by norm_num at *; linarith
  have hlogThreshold : (194 / 10 : ℝ) < Real.log ((2 : ℝ) ^ 28) := by
    rw [Real.log_pow]
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hlog : (194 / 10 : ℝ) < Real.log j :=
    lt_of_lt_of_le hlogThreshold (Real.log_le_log (by positivity) hthreshold)
  have hlower : j * Real.log j < (poolMaximum n : ℝ) := poolMaximum_lower lower n
  have hmax : (7365505384 : ℝ) < (poolMaximum n : ℝ) := by nlinarith
  exact_mod_cast hmax

/-- In the first FW band (`19485 ≤ n`), the active even-grid center capacity satisfies
`86 * X - 2 ≤ 2 * evenGridCenter R`. -/
theorem fw_first_band_evenGridCenter_lower {n R : ℕ} (hnlo : 19485 ≤ n)
    (hcap : 2 * (((n / 450) * poolMaximum n) / 2) ≤ evenGridCenter R) :
    (86 : ℝ) * (poolMaximum n : ℝ) - 2 ≤ 2 * (evenGridCenter R : ℝ) := by
  have hdiv : 43 ≤ n / 450 := by omega
  have hmul : 43 * poolMaximum n ≤ (n / 450) * poolMaximum n :=
    Nat.mul_le_mul_right (poolMaximum n) hdiv
  have hnat : 86 * poolMaximum n ≤ 2 * evenGridCenter R + 2 := by omega
  have hreal : (86 : ℝ) * (poolMaximum n : ℝ) ≤ 2 * (evenGridCenter R : ℝ) + 2 := by
    exact_mod_cast hnat
  linarith

private theorem fw_first_band_mainSum_lower_arith {n c : ℕ} {M S ν P : ℝ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hc : c = n - 12 * (5 + 16 + 3 * (n / 450) + 238))
    (hX7B : 7365505384 < poolMaximum n)
    (hP : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤ P)
    (hmean : |ν - P| ≤ (11 / 100 : ℝ) * (poolMaximum n : ℝ))
    (hS : 0 ≤ S)
    (htrans : |M - (S + (c : ℝ) * ν)| ≤ (poolMaximum n : ℝ)) :
    (5560 : ℝ) * (poolMaximum n : ℝ) ≤ M ∧ (4 * 10 ^ 13 : ℝ) < M := by
  have hcLoNat : 14793 ≤ c := by
    have := Nat.mul_div_le n 450
    omega
  have hcLo : (14793 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcLoNat
  have hX7B' : (7365505384 : ℝ) < (poolMaximum n : ℝ) := by exact_mod_cast hX7B
  have hmeanLo := (abs_le.mp hmean).1
  have hν : (47 / 125 : ℝ) * (poolMaximum n : ℝ) ≤ ν := by linarith
  have hprod : (14793 : ℝ) * ((47 / 125 : ℝ) * (poolMaximum n : ℝ)) ≤ (c : ℝ) * ν :=
    mul_le_mul hcLo hν (by positivity) (by positivity)
  have htransLo := (abs_le.mp htrans).1
  have h5560 : (5560 : ℝ) * (poolMaximum n : ℝ) ≤ M := by linarith
  refine ⟨h5560, ?_⟩
  nlinarith

/-- Lower bound on `mainSum (σ.trans cy)` in the first FW band. -/
theorem fw_projected_cy_spare_first_band_mainSum_lower
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hodd : Odd n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) (fwSelectedThetaChoice hnlo otherChoice))
    (p : Fin 3 → Equiv.Perm (Fin n)) (oldReference : Cell n ≃ Fin (n * n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs
      (fwSelectedThetaChoice hnlo otherChoice)
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
      f.hrows f.hcols p f.ordered oldReference roles)
    (hexp : ∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
      500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card)
    (target : Fin n → ℕ) (hprime : ∀ i, Nat.Prime (target i)) (htodd : ∀ i, Odd (target i))
    (htotal : (∑ i, target i) = Lucas.poolTotal n)
    (htarget : ∀ i, |(target i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
      (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240) :
    let result := fw_projected_cy_spare_transported_target_baseline bmor lower upper hnlo hnhi hodd
      otherChoice f p oldReference roles net hexp target hprime htodd htotal htarget
    let cy := Classical.choose result
    let σ := Classical.choose (Classical.choose_spec result)
    (5560 : ℝ) * (poolMaximum n : ℝ) ≤ (mainSum (σ.trans cy) : ℝ) ∧
    (4 * 10 ^ 13 : ℝ) < (mainSum (σ.trans cy) : ℝ) := by
  classical
  dsimp only
  have hpoolMean := (fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo hnhi).1
  have hX7BNat := fw_poolMaximum_gt_seven_billion lower hnlo
  let choice := fwSelectedThetaChoice hnlo otherChoice
  let full := fwThetaFamilyFull f
  let spare := packedRectangleSupport f.hs choice \ activeRectangleSupport f.hs choice
    (fwActiveRectangleLabels n f.stages.length f.stageCap)
  have hgeom := fw_role_support_for_trace_networks f.stageCap f.hrect f.hseedrect f.hwide f.hoff f.hs choice
    f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc f.hrows f.hcols
  have hspare : full \ roles = spare := by
    rw [net.roles_eq]
    simpa only [full, spare, fwThetaFamilyFull] using hgeom.2.2.2.1
  have hsub : spare ⊆ full := by
    rw [← hspare]
    exact Finset.sdiff_subset
  have hm := (fw_projected_reference_unused_mean_sigma11 bmor lower upper hnlo hnhi choice f p oldReference roles net).2.2.2.2
  have hmean : |centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue -
      (Lucas.poolTotal n : ℝ) / (n * n : ℕ)| ≤ (11 / 100 : ℝ) * poolMaximum n := by
    simpa only [full, prescribedPoolValues_mean] using hm
  have hsdiff : (mainCells n \ full).card = n - 12 * (5 + 16 + 3 * (n / 450) + 238) :=
    (fw_selected_full_diagonal_counts hnlo otherChoice f).2.2.1
  let result := fw_projected_cy_spare_transported_target_baseline bmor lower upper hnlo hnhi hodd
    otherChoice f p oldReference roles net hexp target hprime htodd htotal htarget
  let cy := Classical.choose result
  let σ := Classical.choose (Classical.choose_spec result)
  have facts := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec result))
  have htransMain := facts.2.2.2.1
  have hoff := facts.2.2.2.2.2.1
  have hunused := (off_support_reservation_value_images full spare hsub σ hoff oldReference).2.2
  rw [← hunused] at hmean
  exact fw_first_band_mainSum_lower_arith hnlo hnhi hsdiff hX7BNat hpoolMean hmean
    (Finset.sum_nonneg (fun z _ => Nat.cast_nonneg (entry (σ.trans oldReference) z))) htransMain

/-- Reachable overlap subinterval `(b, c]` for any square `out : Cell n ≃ Fin (n * n)`
satisfying the post-routing row/column primality, diagonal difference `< 27 * X`,
main-diagonal lower bound, and active even-grid guarantees. -/
theorem fw_first_band_reachable_diagonal_of_square
    (lower : RSIndexLower)
    {n : ℕ} (hnlo : 19485 ≤ n) (hodd : Odd n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
    (out : Cell n ≃ Fin (n * n))
    (hr : ∀ i, Nat.Prime (rowSum out i))
    (hc : ∀ i, Nat.Prime (columnSum out i))
    (hdiff27 : |(mainSum out : ℝ) - (antiSum out : ℝ)| < 32 * (poolMaximum n : ℝ))
    (hmain5560 : (5560 : ℝ) * (poolMaximum n : ℝ) ≤ (mainSum out : ℝ))
    (_hmain4e13 : (4 * 10 ^ 13 : ℝ) < (mainSum out : ℝ))
    (hgrids : ∀ side,
      CompleteEvenGrid ((fwActiveRectangleLabels n f.stages.length f.stageCap).filter fun i => choice i = side)
        (fwOrderedCanonicalRectangleGap f) (fwCanonicalFamilyRadius f side) ∧
      2 ∣ fwCanonicalFamilyRadius f side ∧
      2 * ((n / 450) * poolMaximum n) ≤ fwCanonicalFamilyRadius f side ∧
      2 * (((n / 450) * poolMaximum n) / 2) ≤ evenGridCenter (fwCanonicalFamilyRadius f side))
    (hcornerGap : ∀ i ∈ fwActiveRectangleLabels n f.stages.length f.stageCap,
      entry out (packedRectangleCorner f.hs choice (i, 1)) =
        entry out (packedRectangleCorner f.hs choice (i, 0)) + fwOrderedCanonicalRectangleGap f i ∧
      entry out (packedRectangleCorner f.hs choice (i, 2)) =
        entry out (packedRectangleCorner f.hs choice (i, 3)) + fwOrderedCanonicalRectangleGap f i) :
    let L := max (mainSum out) (antiSum out)
    let b : ℝ := (L : ℝ) + (poolMaximum n : ℝ)
    let c : ℝ := (L : ℝ) + 53 * (poolMaximum n : ℝ)
    (4 * 10 ^ 13 : ℝ) < b ∧
    (5560 : ℝ) * (poolMaximum n : ℝ) ≤ b ∧
    c ≤ ((n + 53 : ℕ) : ℝ) * (poolMaximum n : ℝ) ∧
    c - b = 52 * (poolMaximum n : ℝ) ∧
    (mainSum out : ℝ) ≤ b ∧
    c ≤ (mainSum out : ℝ) + 2 * (evenGridCenter (fwCanonicalFamilyRadius f true) : ℝ) ∧
    (antiSum out : ℝ) ≤ b ∧
    c ≤ (antiSum out : ℝ) + 2 * (evenGridCenter (fwCanonicalFamilyRadius f false) : ℝ) ∧
    ((apInterval b c 2 1).Nonempty → HasSquare n) := by
  classical
  dsimp only
  let labels := fwActiveRectangleLabels n f.stages.length f.stageCap
  let gap := fwOrderedCanonicalRectangleGap f
  let L := max (mainSum out) (antiSum out)
  let b : ℝ := (L : ℝ) + (poolMaximum n : ℝ)
  let c : ℝ := (L : ℝ) + 53 * (poolMaximum n : ℝ)
  have hX7B : (7365505384 : ℝ) < (poolMaximum n : ℝ) := by
    exact_mod_cast fw_poolMaximum_gt_seven_billion lower hnlo
  have hLM : (mainSum out : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.le_max_left (mainSum out) (antiSum out)
  have hLA : (antiSum out : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.le_max_right (mainSum out) (antiSum out)
  have hLdiff := abs_lt.mp hdiff27
  have hLleM : (L : ℝ) ≤ (mainSum out : ℝ) + 32 * (poolMaximum n : ℝ) := by
    rcases max_choice (mainSum out) (antiSum out) with hM | hA
    · have hM' : (L : ℝ) = (mainSum out : ℝ) := by exact_mod_cast hM
      linarith
    · have hA' : (L : ℝ) = (antiSum out : ℝ) := by exact_mod_cast hA
      linarith
  have hLleA : (L : ℝ) ≤ (antiSum out : ℝ) + 32 * (poolMaximum n : ℝ) := by
    rcases max_choice (mainSum out) (antiSum out) with hM | hA
    · have hM' : (L : ℝ) = (mainSum out : ℝ) := by exact_mod_cast hM
      linarith
    · have hA' : (L : ℝ) = (antiSum out : ℝ) := by exact_mod_cast hA
      linarith
  have hdiagUpper := physical_diagonal_sum_le out
  have hLUpperNat : L ≤ n * poolMaximum n := max_le hdiagUpper.1 hdiagUpper.2
  have hLUpper : (L : ℝ) ≤ (n : ℝ) * (poolMaximum n : ℝ) := by exact_mod_cast hLUpperNat
  have hcapTrue := fw_first_band_evenGridCenter_lower hnlo (hgrids true).2.2.2
  have hcapFalse := fw_first_band_evenGridCenter_lower hnlo (hgrids false).2.2.2
  have hb4e13 : (4 * 10 ^ 13 : ℝ) < b := by dsimp [b]; linarith
  have hb5560 : (5560 : ℝ) * (poolMaximum n : ℝ) ≤ b := by dsimp [b]; linarith
  have hcUpper : c ≤ ((n + 53 : ℕ) : ℝ) * (poolMaximum n : ℝ) := by
    dsimp [c]
    push_cast
    linarith
  have hcb : c - b = 52 * (poolMaximum n : ℝ) := by dsimp [b, c]; ring
  have hmb : (mainSum out : ℝ) ≤ b := by dsimp [b]; linarith
  have hmc : c ≤ (mainSum out : ℝ) + 2 * (evenGridCenter (fwCanonicalFamilyRadius f true) : ℝ) := by
    dsimp [c]; linarith
  have hab : (antiSum out : ℝ) ≤ b := by dsimp [b]; linarith
  have hac : c ≤ (antiSum out : ℝ) + 2 * (evenGridCenter (fwCanonicalFamilyRadius f false) : ℝ) := by
    dsimp [c]; linarith
  refine ⟨hb4e13, hb5560, hcUpper, hcb, hmb, hmc, hab, hac, ?_⟩
  intro hne
  obtain ⟨q, hqmem⟩ := hne
  have ⟨hqprime, hqlo, hqhi, _⟩ := (mem_apInterval_iff b c 2 1 (by linarith) (by linarith) q).mp hqmem
  have hqne : q ≠ 2 := by
    intro heq
    subst q
    norm_num at hqlo
    linarith
  have hqodd : Odd q := Nat.odd_iff.mpr (hqprime.eq_two_or_odd.resolve_left hqne)
  have hmlo : (mainSum out : ℤ) ≤ q := by
    have h : (mainSum out : ℝ) ≤ (q : ℝ) := hmb.trans (le_of_lt hqlo)
    exact_mod_cast h
  have hmhi : (q : ℤ) ≤ (mainSum out : ℤ) + 2 * (evenGridCenter (fwCanonicalFamilyRadius f true) : ℤ) := by
    have h : (q : ℝ) ≤ (mainSum out : ℝ) + 2 * (evenGridCenter (fwCanonicalFamilyRadius f true) : ℝ) :=
      hqhi.trans hmc
    exact_mod_cast h
  have halo : (antiSum out : ℤ) ≤ q := by
    have h : (antiSum out : ℝ) ≤ (q : ℝ) := hab.trans (le_of_lt hqlo)
    exact_mod_cast h
  have hahi : (q : ℤ) ≤ (antiSum out : ℤ) + 2 * (evenGridCenter (fwCanonicalFamilyRadius f false) : ℤ) := by
    have h : (q : ℝ) ≤ (antiSum out : ℝ) + 2 * (evenGridCenter (fwCanonicalFamilyRadius f false) : ℝ) :=
      hqhi.trans hac
    exact_mod_cast h
  have hL3 : 3 ≤ fwJointRectangleCount n 254 :=
    Nat.le_trans (by decide) f.hrect
  have hgaps : ∀ i ∈ labels,
      entry out (RectanglePacking.firstRow f.hs i, RectanglePacking.secondColumn f.hs choice i) =
        entry out (RectanglePacking.firstRow f.hs i, RectanglePacking.firstColumn f.hs choice i) + gap i ∧
      entry out (RectanglePacking.secondRow f.hs i, RectanglePacking.firstColumn f.hs choice i) =
        entry out (RectanglePacking.secondRow f.hs i, RectanglePacking.secondColumn f.hs choice i) + gap i := by
    intro i hi
    have h := hcornerGap i hi
    have h0 : packedRectangleCorner f.hs choice (i, 0) =
        (RectanglePacking.firstRow f.hs i, RectanglePacking.firstColumn f.hs choice i) := rfl
    have h1 : packedRectangleCorner f.hs choice (i, 1) =
        (RectanglePacking.firstRow f.hs i, RectanglePacking.secondColumn f.hs choice i) := rfl
    have h2 : packedRectangleCorner f.hs choice (i, 2) =
        (RectanglePacking.secondRow f.hs i, RectanglePacking.firstColumn f.hs choice i) := rfl
    have h3 : packedRectangleCorner f.hs choice (i, 3) =
        (RectanglePacking.secondRow f.hs i, RectanglePacking.secondColumn f.hs choice i) := rfl
    rwa [h0, h1, h2, h3] at h
  have hprotect : ∀ z ∈ (∅ : Finset (Cell n)), ∀ i ∈ labels,
      z ∉ rectangleCells (RectanglePacking.firstRow f.hs i) (RectanglePacking.secondRow f.hs i)
        (RectanglePacking.firstColumn f.hs choice i) (RectanglePacking.secondColumn f.hs choice i) := by
    intro z hz
    exact False.elim (Finset.notMem_empty z hz)
  let i0 : Fin n := ⟨0, Nat.lt_of_lt_of_le (by decide) hnlo⟩
  exact (packed_prime_diagonal_repair_reachable_target f.hs hL3 hodd choice gap labels
      (fwCanonicalFamilyRadius f true) (fwCanonicalFamilyRadius f false)
      out out ∅ (hgrids true).1 (hgrids false).1
      hgaps hprotect (fun _ _ => rfl) rfl rfl
      hr hc
      (fun _ => q) i0 hqprime hqodd
      ⟨sub_nonneg.mpr hmlo, sub_le_iff_le_add'.mpr hmhi⟩
      ⟨sub_nonneg.mpr halo, sub_le_iff_le_add'.mpr hahi⟩).elim
    fun _ hbefore => hbefore.2.2.2.elim fun finalSq hfinal => ⟨finalSq, hfinal.2.2.2.2.1⟩

/-- Reachable overlap subinterval `(b, c]` on the output of
`fw_projected_cy_spare_original_active_output_grids`. -/
theorem fw_first_band_reachable_diagonal_subinterval
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hodd : Odd n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) (fwSelectedThetaChoice hnlo otherChoice))
    (p : Fin 3 → Equiv.Perm (Fin n))
    (intermediate oldReference : Cell n ≃ Fin (n * n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs
      (fwSelectedThetaChoice hnlo otherChoice)
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
      f.hrows f.hcols p f.ordered oldReference roles)
    (hexp : ∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
      500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card)
    (target : Fin n → ℕ) (hprime : ∀ i, Nat.Prime (target i)) (htodd : ∀ i, Odd (target i))
    (htotal : (∑ i, target i) = Lucas.poolTotal n)
    (htarget : ∀ i, |(target i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
      (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240)
    (fresh : FWThetaFreshWideProjection f intermediate oldReference)
    (hg : FWThetaGrowthDiagonalWitness n (fwJointRectangleCount n 254)
      (fwSelectedThetaChoice hnlo otherChoice) f) :
    let result := fw_projected_cy_spare_transported_target_baseline bmor lower upper hnlo hnhi hodd
      otherChoice f p oldReference roles net hexp target hprime htodd htotal htarget
    let out := Classical.choose (Classical.choose_spec (Classical.choose_spec result))
    let L := max (mainSum out) (antiSum out)
    let b : ℝ := (L : ℝ) + (poolMaximum n : ℝ)
    let c : ℝ := (L : ℝ) + 53 * (poolMaximum n : ℝ)
    (4 * 10 ^ 13 : ℝ) < b ∧
    (5560 : ℝ) * (poolMaximum n : ℝ) ≤ b ∧
    c ≤ ((n + 53 : ℕ) : ℝ) * (poolMaximum n : ℝ) ∧
    c - b = 52 * (poolMaximum n : ℝ) ∧
    (mainSum out : ℝ) ≤ b ∧
    c ≤ (mainSum out : ℝ) + 2 * (evenGridCenter (fwCanonicalFamilyRadius f true) : ℝ) ∧
    (antiSum out : ℝ) ≤ b ∧
    c ≤ (antiSum out : ℝ) + 2 * (evenGridCenter (fwCanonicalFamilyRadius f false) : ℝ) ∧
    ((apInterval b c 2 1).Nonempty → HasSquare n) := by
  dsimp only
  let result := fw_projected_cy_spare_transported_target_baseline bmor lower upper hnlo hnhi hodd
    otherChoice f p oldReference roles net hexp target hprime htodd htotal htarget
  let cy := Classical.choose result
  let σ := Classical.choose (Classical.choose_spec result)
  let out := Classical.choose (Classical.choose_spec (Classical.choose_spec result))
  have facts := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec result))
  have hr := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmainOut := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hantiOut := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hrouted := fw_projected_cy_spare_original_active_output_grids bmor lower upper hnlo hnhi hodd
    otherChoice f p oldReference roles net hexp target hprime htodd htotal htarget fresh.radius_lower
  have hdiff27 := fw_projected_cy_spare_first_band_diagonal_difference_lt_27 bmor lower upper hnlo hnhi hodd
    otherChoice f p intermediate oldReference roles net hg fresh hexp target hprime htodd htotal htarget
  have hdiff27' : |(mainSum out : ℝ) - (antiSum out : ℝ)| < 32 * (poolMaximum n : ℝ) := by
    rw [hmainOut, hantiOut]
    exact hdiff27
  have hmainLo := fw_projected_cy_spare_first_band_mainSum_lower bmor lower upper hnlo hnhi hodd
    otherChoice f p oldReference roles net hexp target hprime htodd htotal htarget
  have hmainLo' : (5560 : ℝ) * (poolMaximum n : ℝ) ≤ (mainSum out : ℝ) ∧
      (4 * 10 ^ 13 : ℝ) < (mainSum out : ℝ) := by
    rw [hmainOut]
    exact hmainLo
  exact fw_first_band_reachable_diagonal_of_square lower hnlo hodd
    (fwSelectedThetaChoice hnlo otherChoice) f out
    (fun r => (hr r).2) (fun c => (hc c).2)
    hdiff27' hmainLo'.1 hmainLo'.2 hrouted.2.2.1 hrouted.2.2.2.2

/-- Complete first-band route reduction to seed supply, row/column target vector,
and odd-prime nonemptiness on the reachable diagonal subinterval. -/
theorem fw_theta_fresh_first_band_hasSquare_of_targets_and_diag_prime
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta)
    (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hodd : Odd n)
    (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hseedPrime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hseedCount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card)
    (target : Fin n → ℕ) (hprime : ∀ i, Nat.Prime (target i)) (htodd : ∀ i, Odd (target i))
    (htotal : (∑ i, target i) = Lucas.poolTotal n)
    (htarget : ∀ i, |(target i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
      (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240)
    (hdiagPrime : ∀ b c : ℝ,
      (4 * 10 ^ 13 : ℝ) < b →
      (5560 : ℝ) * (poolMaximum n : ℝ) ≤ b →
      c ≤ ((n + 53 : ℕ) : ℝ) * (poolMaximum n : ℝ) →
      c - b = 52 * (poolMaximum n : ℝ) →
      (apInterval b c 2 1).Nonempty) :
    HasSquare n := by
  classical
  let otherChoice : Fin (fwJointRectangleCount n 254) → Bool := fun _ => false
  let a0 : Cell n ≃ Fin (n * n) := finProdFinEquiv
  exact (fw_theta_fresh_spare_output_grids mv bmor upper lower sharp upperSharp
      hnlo hnhi hodd otherChoice a0 seeds hseed hseedPrime hseedCount
      target hprime htodd htotal htarget).2.elim fun p hp =>
    hp.elim fun f hf => hf.elim fun w hw => hw.elim fun reference href =>
    href.elim fun roles hroles => hroles.elim fun net hnet =>
    hnet.elim fun hexp hfresh0 => hfresh0.elim fun fresh hrest =>
    Nonempty.elim hrest.1 fun hg =>
      have hsub := fw_first_band_reachable_diagonal_subinterval bmor lower upper hnlo hnhi hodd
        otherChoice f p w.intermediate reference roles net hexp target hprime htodd htotal htarget fresh hg
      hsub.2.2.2.2.2.2.2.2 (hdiagPrime _ _ hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2.1)

end
end Sude
