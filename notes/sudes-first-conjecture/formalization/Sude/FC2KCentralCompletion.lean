import Sude.CYDiagonalWidenedCompletion
import Sude.CentralPostInputs
import Sude.DiagonalLineTransfer

/-!
# Sharp Central-Band Diagonal & Off-Diagonal Completion (`FC2KCentralCompletion`)

Replaces the coarse `[0, X]` diagonal preassignment of `CYDiagonalWidenedCompletion`
with `central_place_odd_diagonals_exact_pool` centered directly at `c := μ₀` (`η := ε * X`),
followed by `cy_full_keepout_sharp_central_completion`.

This sharpens the row/column completion bound from `(4 + (7 + 1 / n) * ε) * X` down to
`(1 + 10 * ε) * X` (`1.60 * X` at `ε = 3 / 50`) and both diagonal bounds down to
`2 * ε * X` and `(201 / 100) * ε * X`.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false

/-- Algebraic simplification of the transferred row/column completion bound for `n ≥ 20`. -/
private theorem fc2k_central_completion_coeff_le {n : ℕ} (hn : 20 ≤ n) {ε X : ℝ}
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

/-- Available odd primes in a subinterval `(lo, hi]` outside `reserved.image (entry a)`
inject into the filtered `actualUnusedPool a reserved`. -/
private theorem availableInterval_le_filter_actualUnusedPool {n : ℕ}
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

/-- BMOR half-window unused-pool stock bound on `(lo, hi]` of width `(ε / 2) * X`. -/
private theorem bmor_subwindow_unused_stock_bound (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    {n : ℕ} (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (lo hi ε : ℝ) (Dold need : ℕ)
    (hlo1 : 1 ≤ lo) (hhiX : hi ≤ (poolMaximum n : ℝ))
    (hlen : hi - lo = (ε / 2) * (poolMaximum n : ℝ))
    (hε : 0 < ε)
    (hdeleted : (apInterval lo hi 2 1 ∩ reserved.image (entry a)).card ≤ Dold)
    (hneed : need ≤ 2 * n - 1)
    (hgate : ((2 * n - 1 : ℕ) : ℝ) ≤
      ((ε / 2) * (poolMaximum n : ℝ) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n : ℝ)) /
        Real.log (poolMaximum n : ℝ) - (Dold : ℝ)) :
    need ≤
      ((actualUnusedPool a reserved).filter
        (fun v => lo < centralPoolValue v ∧ centralPoolValue v ≤ hi)).card := by
  let X : ℝ := poolMaximum n
  have hXgt1 : (1 : ℝ) < X := by
    dsimp [X]
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) (poolMaximum_prime n).two_le)
  have hXpos : 0 < X := by linarith
  have hlogPos : 0 < Real.log X := Real.log_pos hXgt1
  have hbc : lo ≤ hi := by
    have : 0 < hi - lo := by rw [hlen]; positivity
    linarith
  have hs := bmor_two_pool_interval_supply bmor upper n lo hi hn hnmax hlo1 hbc hhiX
  have hsum := Finset.card_sdiff_add_card_inter (apInterval lo hi 2 1) (reserved.image (entry a))
  have hsum' : (availableInterval lo hi 2 1 (reserved.image (entry a))).card +
      (apInterval lo hi 2 1 ∩ reserved.image (entry a)).card =
      (apInterval lo hi 2 1).card := hsum
  have hsumR : ((availableInterval lo hi 2 1 (reserved.image (entry a))).card : ℝ) +
      ((apInterval lo hi 2 1 ∩ reserved.image (entry a)).card : ℝ) =
      ((apInterval lo hi 2 1).card : ℝ) := by exact_mod_cast hsum'
  have hdelR : ((apInterval lo hi 2 1 ∩ reserved.image (entry a)).card : ℝ) ≤ Dold := by
    exact_mod_cast hdeleted
  have hslo : Real.sqrt lo ≤ Real.sqrt X := Real.sqrt_le_sqrt (le_trans hbc hhiX)
  have hshi : Real.sqrt hi ≤ Real.sqrt X := Real.sqrt_le_sqrt hhiX
  have hnum : (ε / 2) * X - (1036 / 125 : ℝ) * Real.sqrt X ≤
      (hi - lo) - (518 / 125 : ℝ) * (Real.sqrt lo + Real.sqrt hi) := by
    dsimp [X] at hlen ⊢
    rw [hlen]
    linarith
  have hquot : ((ε / 2) * X - (1036 / 125 : ℝ) * Real.sqrt X) / Real.log X ≤
      ((hi - lo) - (518 / 125 : ℝ) * (Real.sqrt lo + Real.sqrt hi)) / Real.log X :=
    div_le_div_of_nonneg_right hnum hlogPos.le
  have havailR : ((2 * n - 1 : ℕ) : ℝ) ≤
      ((availableInterval lo hi 2 1 (reserved.image (entry a))).card : ℝ) := by
    dsimp [X] at hquot hs hgate
    linarith [hgate, hquot, hs.1, hsumR, hdelR]
  have havailN : 2 * n - 1 ≤ (availableInterval lo hi 2 1 (reserved.image (entry a))).card := by
    exact_mod_cast havailR
  exact hneed.trans (havailN.trans
    (availableInterval_le_filter_actualUnusedPool a reserved lo hi hlo1 hbc hhiX))

/-- Sharp central-band diagonal and off-diagonal completion with separate half-window
and full-window deletion budgets `DoldHalf` and `DoldFull`. -/
private theorem fc2k_central_band_sharp_completion_aux (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    {L n : ℕ} (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (hn : 20 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hodd : Odd n) (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols)
    (hload : 4 * (2 * (rows.length + cols.length) + 4) ≤ n)
    (a : Cell n ≃ Fin (n * n)) (full : Finset (Cell n))
    (hfull : full = packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols))
    (ε : ℝ) (DoldHalf DoldFull : ℕ) (hε : 0 < ε)
    (hreserve : 4 * full.card ≤ n * n)
    (hleft : 1 ≤ centralEntriesMean (actualUnusedPool a full) centralPoolValue -
      ε * (poolMaximum n : ℝ) - 6 * (ε * (poolMaximum n : ℝ)) / ((n * n - 1 : ℕ) : ℝ))
    (hright : centralEntriesMean (actualUnusedPool a full) centralPoolValue +
      ε * (poolMaximum n : ℝ) + 6 * (ε * (poolMaximum n : ℝ)) / ((n * n - 1 : ℕ) : ℝ) ≤
      (poolMaximum n : ℝ))
    (hdeletedLow :
      (apInterval
        (centralEntriesMean (actualUnusedPool a full) centralPoolValue - ε * (poolMaximum n : ℝ))
        (centralEntriesMean (actualUnusedPool a full) centralPoolValue -
          (ε * (poolMaximum n : ℝ)) / 2)
        2 1 ∩ full.image (entry a)).card ≤ DoldHalf)
    (hdeletedHigh :
      (apInterval
        (centralEntriesMean (actualUnusedPool a full) centralPoolValue +
          (ε * (poolMaximum n : ℝ)) / 2)
        (centralEntriesMean (actualUnusedPool a full) centralPoolValue + ε * (poolMaximum n : ℝ))
        2 1 ∩ full.image (entry a)).card ≤ DoldHalf)
    (hdeletedFull :
      (apInterval
        (centralEntriesMean (actualUnusedPool a full) centralPoolValue -
          ε * (poolMaximum n : ℝ) - 6 * (ε * (poolMaximum n : ℝ)) / ((n * n - 1 : ℕ) : ℝ))
        (centralEntriesMean (actualUnusedPool a full) centralPoolValue +
          ε * (poolMaximum n : ℝ) + 6 * (ε * (poolMaximum n : ℝ)) / ((n * n - 1 : ℕ) : ℝ))
        2 1 ∩ full.image (entry a)).card ≤ DoldFull)
    (hhalfGate :
      ((2 * n - 1 : ℕ) : ℝ) ≤
        ((ε / 2) * (poolMaximum n : ℝ) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n : ℝ)) /
          Real.log (poolMaximum n : ℝ) - (DoldHalf : ℝ))
    (hfullGate :
      ((3 * n + 1 : ℕ) : ℝ) ≤
        (2 * (ε * (poolMaximum n : ℝ)) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n : ℝ)) /
          Real.log (poolMaximum n : ℝ) - (((DoldFull + (2 * n - 1) : ℕ)) : ℝ)) :
    ∃ b c : Cell n ≃ Fin (n * n),
      (∀ z ∈ full, entry b z = entry a z) ∧
      (∀ z ∈ full ∪ unreservedDiagonalCells full, entry c z = entry b z) ∧
      (∀ z ∈ full, entry c z = entry a z) ∧
      |(mainSum c : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry a z : ℝ)) +
        ((mainCells n \ full).card : ℝ) *
          centralEntriesMean (actualUnusedPool a full) centralPoolValue)| ≤
        2 * ε * (poolMaximum n : ℝ) ∧
      |(antiSum c : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry a z : ℝ)) +
        ((antiCells n \ full).card : ℝ) *
          centralEntriesMean (actualUnusedPool a full) centralPoolValue)| ≤
        (201 / 100 : ℝ) * ε * (poolMaximum n : ℝ) ∧
      (∀ i, |(rowSum c i : ℝ) - ((∑ z ∈ rowCells i ∩ full, (entry a z : ℝ)) +
        ((rowCells i \ full).card : ℝ) *
          centralEntriesMean (actualUnusedPool a full) centralPoolValue)| <
        (1 + 10 * ε) * (poolMaximum n : ℝ)) ∧
      (∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ full, (entry a z : ℝ)) +
        ((columnCells i \ full).card : ℝ) *
          centralEntriesMean (actualUnusedPool a full) centralPoolValue)| <
        (1 + 10 * ε) * (poolMaximum n : ℝ)) ∧
      mainSum c = mainSum b ∧ antiSum c = antiSum b ∧
      Set.range (entry c) = pool n ∧ Function.Injective (entry c) := by
  let final := full ∪ unreservedDiagonalCells full
  let μ₀ := centralEntriesMean (actualUnusedPool a full) centralPoolValue
  let X : ℝ := poolMaximum n
  let η : ℝ := ε * X
  let δ : ℝ := 6 * η / ((n * n - 1 : ℕ) : ℝ)
  have hXgt1 : (1 : ℝ) < X := by
    dsimp [X]
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) (poolMaximum_prime n).two_le)
  have hXpos : 0 < X := by linarith
  have hηpos : 0 < η := mul_pos hε hXpos
  have hδnonneg : 0 ≤ δ := by dsimp [δ]; positivity
  have hcenter : centralCell n (by omega) ∉ full := by
    rw [hfull]
    exact fw_full_keepout_avoids_center hs (by omega) choice rows cols hrows hcols
  obtain ⟨hXcard, hYcard, hZcard, _, _, _, hXY, hXZ, _, hmainPart, hantiPart⟩ :=
    central_free_diagonal_geometry (by omega : 0 < n) hodd full hcenter
  have hdiagNeed : 1 + (centralFreeMain (by omega) full).card +
      (centralFreeAnti (by omega) full).card ≤ 2 * n - 1 := by
    omega
  have hlowStock : 1 + (centralFreeMain (by omega) full).card +
      (centralFreeAnti (by omega) full).card ≤
      ((actualUnusedPool a full).filter
        (fun v => μ₀ - η < centralPoolValue v ∧ centralPoolValue v ≤ μ₀ - η / 2)).card :=
    bmor_subwindow_unused_stock_bound bmor upper (by omega) hnmax a full
      (μ₀ - η) (μ₀ - η / 2) ε DoldHalf _
      (by dsimp [μ₀, η, δ, X] at *; linarith)
      (by dsimp [μ₀, η, δ, X] at *; linarith)
      (by dsimp [η, X]; ring) hε
      hdeletedLow hdiagNeed hhalfGate
  have hhighStock : 1 + (centralFreeMain (by omega) full).card +
      (centralFreeAnti (by omega) full).card ≤
      ((actualUnusedPool a full).filter
        (fun v => μ₀ + η / 2 < centralPoolValue v ∧ centralPoolValue v ≤ μ₀ + η)).card :=
    bmor_subwindow_unused_stock_bound bmor upper (by omega) hnmax a full
      (μ₀ + η / 2) (μ₀ + η) ε DoldHalf _
      (by dsimp [μ₀, η, δ, X] at *; linarith)
      (by dsimp [μ₀, η, δ, X] at *; linarith)
      (by dsimp [η, X]; ring) hε
      hdeletedHigh hdiagNeed hhalfGate
  obtain ⟨b, _A, _B, _C, _, _, _, _, _, _, hfixed, hcentral, _, hcount, _, _, hshiftRaw,
      hmain, hanti, _, _⟩ :=
    central_place_odd_diagonals_exact_pool a full μ₀ η hηpos hn hodd hcenter hreserve
      (by dsimp only [μ₀]; rw [sub_self, abs_zero]; positivity) hlowStock hhighStock
  let μ₁ := centralEntriesMean (actualUnusedPool b final) centralPoolValue
  have hshift : |μ₁ - μ₀| ≤ δ := by
    have hu := diagonal_mean_shift_uniform n (actualUnusedPool b final).card η
      (by omega) hηpos.le hcount
    exact hshiftRaw.trans hu
  have hleftb : 1 ≤ μ₁ - η := by
    have hm := (abs_le.mp hshift).1
    dsimp [μ₀, η, δ, X] at *; linarith
  have hrightb : μ₁ + η ≤ X := by
    have hm := (abs_le.mp hshift).2
    dsimp [μ₀, η, δ, X] at *; linarith
  have hdelPost := post_diagonal_deletions_from_widened_interval a b full μ₀ μ₁ η δ
    (by omega) hodd hfixed hηpos.le hshift (by dsimp [μ₀, η, δ, X] at *; linarith)
  have hdelPost' : (apInterval (μ₁ - η) (μ₁ + η) 2 1 ∩ final.image (entry b)).card ≤
      DoldFull + (2 * n - 1) := by
    change (apInterval (μ₁ - η) (μ₁ + η) 2 1 ∩ final.image (entry b)).card ≤
      (apInterval (μ₀ - η - δ) (μ₀ + η + δ) 2 1 ∩ full.image (entry a)).card + (2 * n - 1) at hdelPost
    change (apInterval (μ₀ - η - δ) (μ₀ + η + δ) 2 1 ∩ full.image (entry a)).card ≤ DoldFull at hdeletedFull
    omega
  have hstockPost := bmor_central_stock_source_bound bmor upper b final ε (DoldFull + (2 * n - 1))
    hε.le (by omega) hnmax hleftb hrightb hdelPost'
  have hstockR : ((3 * n + 1 : ℕ) : ℝ) ≤ (centralExceptionStock b final η).card :=
    hfullGate.trans hstockPost
  have hstockN : 3 * n + 1 ≤ (centralExceptionStock b final η).card := by
    exact_mod_cast hstockR
  have hstockN' : 3 * n + 1 ≤
      (centralExceptionStock b
        ((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
          LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪
          unreservedDiagonalCells (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
            LayerPacking.transposeCells (LayerPacking.layersSupport cols))) η).card := by
    simpa only [final, hfull] using hstockN
  obtain ⟨c, hfixedc', hrowsC', hcolsC', hmainc, hantic, hpool, hinj⟩ :=
    cy_full_keepout_sharp_central_completion hs hL (by omega) hodd choice rows cols
      hrows hcols hload b ε hε.le hstockN'
  have hfixedc : ∀ z ∈ final, entry c z = entry b z := by
    simpa only [final, hfull] using hfixedc'
  have hrowsC : ∀ i, |(rowSum c i : ℝ) - ((∑ z ∈ rowCells i ∩ final, (entry b z : ℝ)) +
      ((rowCells i \ final).card : ℝ) * μ₁)| < (1 + (7 + 1 / (n : ℝ)) * ε) * X := by
    simpa only [final, μ₁, X, hfull] using hrowsC'
  have hcolsC : ∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ final, (entry b z : ℝ)) +
      ((columnCells i \ final).card : ℝ) * μ₁)| < (1 + (7 + 1 / (n : ℝ)) * ε) * X := by
    simpa only [final, μ₁, X, hfull] using hcolsC'
  have htrans := diagonal_preassignment_rows_columns_transfer a b c full μ₀ μ₁ η δ
    ((1 + (7 + 1 / (n : ℝ)) * ε) * X) hηpos.le hδnonneg hfixed hcentral hshift hrowsC hcolsC
  have hcoeff : (1 + (7 + 1 / (n : ℝ)) * ε) * X + 2 * η + (n : ℝ) * δ ≤ (1 + 10 * ε) * X :=
    fc2k_central_completion_coeff_le hn hε hXpos
  have hmainCard : 1 + (centralFreeMain (by omega) full).card = (mainCells n \ full).card := by
    rw [← hmainPart, Finset.card_union_of_disjoint hXY, hXcard]
  have hantiCard : 1 + (centralFreeAnti (by omega) full).card = (antiCells n \ full).card := by
    rw [← hantiPart, Finset.card_union_of_disjoint hXZ, hXcard]
  refine ⟨b, c, hfixed, hfixedc, ?_, ?_, ?_, ?_, ?_, hmainc, hantic, hpool, hinj⟩
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

/-- Sharp central-band diagonal and off-diagonal completion with separate half-window (`DoldHalf`)
and full-window (`DoldFull`) deletion budgets. -/
theorem fc2k_central_band_sharp_completion_two_budgets (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    {L n : ℕ} (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (hn : 20 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hodd : Odd n) (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols)
    (hload : 4 * (2 * (rows.length + cols.length) + 4) ≤ n)
    (a : Cell n ≃ Fin (n * n)) (ε : ℝ) (DoldHalf DoldFull : ℕ) (hε : 0 < ε)
    (hreserve :
      let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      4 * full.card ≤ n * n)
    (hleft :
      let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      let X : ℝ := poolMaximum n
      let δ : ℝ := 6 * (ε * X) / ((n * n - 1 : ℕ) : ℝ)
      1 ≤ centralEntriesMean (actualUnusedPool a full) centralPoolValue - ε * X - δ)
    (hright :
      let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      let X : ℝ := poolMaximum n
      let δ : ℝ := 6 * (ε * X) / ((n * n - 1 : ℕ) : ℝ)
      centralEntriesMean (actualUnusedPool a full) centralPoolValue + ε * X + δ ≤ X)
    (hdeletedLow :
      let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      let X : ℝ := poolMaximum n
      (apInterval
        (centralEntriesMean (actualUnusedPool a full) centralPoolValue - ε * X)
        (centralEntriesMean (actualUnusedPool a full) centralPoolValue - (ε * X) / 2)
        2 1 ∩ full.image (entry a)).card ≤ DoldHalf)
    (hdeletedHigh :
      let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      let X : ℝ := poolMaximum n
      (apInterval
        (centralEntriesMean (actualUnusedPool a full) centralPoolValue + (ε * X) / 2)
        (centralEntriesMean (actualUnusedPool a full) centralPoolValue + ε * X)
        2 1 ∩ full.image (entry a)).card ≤ DoldHalf)
    (hdeletedFull :
      let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      let X : ℝ := poolMaximum n
      let δ : ℝ := 6 * (ε * X) / ((n * n - 1 : ℕ) : ℝ)
      (apInterval
        (centralEntriesMean (actualUnusedPool a full) centralPoolValue - ε * X - δ)
        (centralEntriesMean (actualUnusedPool a full) centralPoolValue + ε * X + δ)
        2 1 ∩ full.image (entry a)).card ≤ DoldFull)
    (hhalfGate :
      let X : ℝ := poolMaximum n
      ((2 * n - 1 : ℕ) : ℝ) ≤
        ((ε / 2) * X - (1036 / 125 : ℝ) * Real.sqrt X) / Real.log X - (DoldHalf : ℝ))
    (hfullGate :
      let X : ℝ := poolMaximum n
      ((3 * n + 1 : ℕ) : ℝ) ≤
        (2 * (ε * X) - (1036 / 125 : ℝ) * Real.sqrt X) / Real.log X -
          (((DoldFull + (2 * n - 1) : ℕ)) : ℝ)) :
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)
    let final := full ∪ unreservedDiagonalCells full
    let μ₀ := centralEntriesMean (actualUnusedPool a full) centralPoolValue
    let X : ℝ := poolMaximum n
    ∃ b c : Cell n ≃ Fin (n * n),
      (∀ z ∈ full, entry b z = entry a z) ∧
      (∀ z ∈ final, entry c z = entry b z) ∧
      (∀ z ∈ full, entry c z = entry a z) ∧
      |(mainSum c : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry a z : ℝ)) +
        ((mainCells n \ full).card : ℝ) * μ₀)| ≤ 2 * ε * X ∧
      |(antiSum c : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry a z : ℝ)) +
        ((antiCells n \ full).card : ℝ) * μ₀)| ≤ (201 / 100 : ℝ) * ε * X ∧
      (∀ i, |(rowSum c i : ℝ) - ((∑ z ∈ rowCells i ∩ full, (entry a z : ℝ)) +
        ((rowCells i \ full).card : ℝ) * μ₀)| < (1 + 10 * ε) * X) ∧
      (∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ full, (entry a z : ℝ)) +
        ((columnCells i \ full).card : ℝ) * μ₀)| < (1 + 10 * ε) * X) ∧
      mainSum c = mainSum b ∧ antiSum c = antiSum b ∧
      Set.range (entry c) = pool n ∧ Function.Injective (entry c) :=
  fc2k_central_band_sharp_completion_aux bmor upper hs hL hn hnmax hodd choice rows cols
    hrows hcols hload a _ rfl ε DoldHalf DoldFull hε hreserve hleft hright
    hdeletedLow hdeletedHigh hdeletedFull hhalfGate hfullGate

/-- Sharp central-band diagonal and off-diagonal completion on one physical keepout `full`. -/
theorem fc2k_central_band_sharp_completion (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    {L n : ℕ} (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (hn : 20 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hodd : Odd n) (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols)
    (hload : 4 * (2 * (rows.length + cols.length) + 4) ≤ n)
    (a : Cell n ≃ Fin (n * n)) (ε : ℝ) (Dold : ℕ) (hε : 0 < ε)
    (hreserve :
      let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      4 * full.card ≤ n * n)
    (hleft :
      let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      let X : ℝ := poolMaximum n
      let δ : ℝ := 6 * (ε * X) / ((n * n - 1 : ℕ) : ℝ)
      1 ≤ centralEntriesMean (actualUnusedPool a full) centralPoolValue - ε * X - δ)
    (hright :
      let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      let X : ℝ := poolMaximum n
      let δ : ℝ := 6 * (ε * X) / ((n * n - 1 : ℕ) : ℝ)
      centralEntriesMean (actualUnusedPool a full) centralPoolValue + ε * X + δ ≤ X)
    (hdeleted :
      let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      let X : ℝ := poolMaximum n
      let δ : ℝ := 6 * (ε * X) / ((n * n - 1 : ℕ) : ℝ)
      (apInterval
        (centralEntriesMean (actualUnusedPool a full) centralPoolValue - ε * X - δ)
        (centralEntriesMean (actualUnusedPool a full) centralPoolValue + ε * X + δ)
        2 1 ∩ full.image (entry a)).card ≤ Dold)
    (hhalfGate :
      let X : ℝ := poolMaximum n
      ((2 * n - 1 : ℕ) : ℝ) ≤
        ((ε / 2) * X - (1036 / 125 : ℝ) * Real.sqrt X) / Real.log X - (Dold : ℝ))
    (hfullGate :
      let X : ℝ := poolMaximum n
      ((3 * n + 1 : ℕ) : ℝ) ≤
        (2 * (ε * X) - (1036 / 125 : ℝ) * Real.sqrt X) / Real.log X -
          (((Dold + (2 * n - 1) : ℕ)) : ℝ)) :
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)
    let final := full ∪ unreservedDiagonalCells full
    let μ₀ := centralEntriesMean (actualUnusedPool a full) centralPoolValue
    let X : ℝ := poolMaximum n
    ∃ b c : Cell n ≃ Fin (n * n),
      (∀ z ∈ full, entry b z = entry a z) ∧
      (∀ z ∈ final, entry c z = entry b z) ∧
      (∀ z ∈ full, entry c z = entry a z) ∧
      |(mainSum c : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry a z : ℝ)) +
        ((mainCells n \ full).card : ℝ) * μ₀)| ≤ 2 * ε * X ∧
      |(antiSum c : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry a z : ℝ)) +
        ((antiCells n \ full).card : ℝ) * μ₀)| ≤ (201 / 100 : ℝ) * ε * X ∧
      (∀ i, |(rowSum c i : ℝ) - ((∑ z ∈ rowCells i ∩ full, (entry a z : ℝ)) +
        ((rowCells i \ full).card : ℝ) * μ₀)| < (1 + 10 * ε) * X) ∧
      (∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ full, (entry a z : ℝ)) +
        ((columnCells i \ full).card : ℝ) * μ₀)| < (1 + 10 * ε) * X) ∧
      mainSum c = mainSum b ∧ antiSum c = antiSum b ∧
      Set.range (entry c) = pool n ∧ Function.Injective (entry c) := by
  let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport cols)
  let X : ℝ := poolMaximum n
  let η : ℝ := ε * X
  let δ : ℝ := 6 * η / ((n * n - 1 : ℕ) : ℝ)
  let μ₀ := centralEntriesMean (actualUnusedPool a full) centralPoolValue
  have hXpos : 0 < X := by
    dsimp [X]
    exact_mod_cast (poolMaximum_prime n).pos
  have hηpos : 0 < η := mul_pos hε hXpos
  have hδnonneg : 0 ≤ δ := by dsimp [δ]; positivity
  have hsubLow :
      (apInterval (μ₀ - η) (μ₀ - η / 2) 2 1 ∩ full.image (entry a)).card ≤ Dold := by
    refine le_trans (Finset.card_le_card ?_) hdeleted
    intro p hp
    have hp1 := (Finset.mem_inter.mp hp).1
    have hp2 := (Finset.mem_inter.mp hp).2
    have hp' := (mem_apInterval_iff (μ₀ - η) (μ₀ - η / 2) 2 1
      (by linarith) (by linarith) p).mp hp1
    exact Finset.mem_inter.mpr ⟨(mem_apInterval_iff (μ₀ - η - δ) (μ₀ + η + δ) 2 1
      (by linarith) (by linarith) p).mpr
      ⟨hp'.1, by linarith [hp'.2.1], by linarith [hp'.2.2.1], hp'.2.2.2⟩, hp2⟩
  have hsubHigh :
      (apInterval (μ₀ + η / 2) (μ₀ + η) 2 1 ∩ full.image (entry a)).card ≤ Dold := by
    refine le_trans (Finset.card_le_card ?_) hdeleted
    intro p hp
    have hp1 := (Finset.mem_inter.mp hp).1
    have hp2 := (Finset.mem_inter.mp hp).2
    have hp' := (mem_apInterval_iff (μ₀ + η / 2) (μ₀ + η) 2 1
      (by linarith) (by linarith) p).mp hp1
    exact Finset.mem_inter.mpr ⟨(mem_apInterval_iff (μ₀ - η - δ) (μ₀ + η + δ) 2 1
      (by linarith) (by linarith) p).mpr
      ⟨hp'.1, by linarith [hp'.2.1], by linarith [hp'.2.2.1], hp'.2.2.2⟩, hp2⟩
  exact fc2k_central_band_sharp_completion_two_budgets bmor upper hs hL hn hnmax hodd choice
    rows cols hrows hcols hload a ε Dold Dold hε hreserve hleft hright
    hsubLow hsubHigh hdeleted hhalfGate hfullGate

end

end Sude
