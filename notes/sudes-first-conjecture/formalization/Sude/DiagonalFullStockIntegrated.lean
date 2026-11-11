import Sude.DiagonalFullStockActualDiagonals
import Sude.DiagonalFullStockLineShift
import Sude.CentralPairDiagonal
import Sude.DiagonalFullStockPostMean

/-! The DQ diagonal and short-line invoices on one physical witness. -/
namespace Sude
noncomputable section

private theorem full_stock_three_x_arithmetic (X n k N : ℝ)
    (hX : 0 ≤ X) (hn : 0 < n) (hk : k ≤ n) (hN : 2*n ≤ N) :
    (5/2 : ℝ)*X + k*(X/N) ≤ 3*X := by
  have hNpos : 0 < N := by linarith
  have hk2 : k / N ≤ 1 / 2 := by
    apply (div_le_iff₀ hNpos).2
    linarith
  have hmul := mul_le_mul_of_nonneg_right hk2 hX
  have hid : k * (X / N) = (k / N) * X := by ring
  rw [hid]
  linarith

/-- One DQ witness simultaneously controls both actual diagonal sums, the
remaining stock, and all short lines meeting at most two free diagonal cells. -/
theorem odd_full_stock_integrated_diagonal_witness_with_mean {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (reserved : Finset (Cell n)) (hn7 : 7 ≤ n) (hodd : Odd n)
    (hcenter : centralCell n (by omega) ∉ reserved)
    (hreserve : 4 * reserved.card ≤ n*n) :
    ∃ b₀ b : Cell n ≃ Fin (n*n), (∀ z ∈ reserved, entry b₀ z = entry a z) ∧ (∀ z ∈ reserved, entry b z = entry a z) ∧
      |(mainSum b : ℝ) - ((∑ z ∈ mainCells n ∩ reserved, (entry a z : ℝ)) +
        ((mainCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (poolMaximum n : ℝ) ∧
      |(antiSum b : ℝ) - ((∑ z ∈ antiCells n ∩ reserved, (entry a z : ℝ)) +
        ((antiCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (3/2 : ℝ) * poolMaximum n ∧
      2*n ≤ (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card ∧
      |centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
        (poolMaximum n : ℝ) / (2 * (actualUnusedPool b₀ (reserved ∪ {centralCell n (by omega)})).card) +
          (poolMaximum n : ℝ) / (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card ∧
      ∀ line : Finset (Cell n), line.card ≤ n → (line ∩ unreservedDiagonalCells reserved).card ≤ 2 →
        |((∑ z ∈ line ∩ (reserved ∪ unreservedDiagonalCells reserved), (entry b z : ℝ)) +
            ((line \ (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) *
              centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue) -
          ((∑ z ∈ line ∩ reserved, (entry a z : ℝ)) +
            ((line \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          3 * (poolMaximum n : ℝ) := by
  classical
  let hn : 0 < n := by omega
  let center := centralCell n hn
  let Y := centralFreeMain hn reserved
  let Z := centralFreeAnti hn reserved
  let R := reserved ∪ {center}
  obtain ⟨_, hYcard, hZcard, _, hYR, hZR, hXY, hXZ, hYZ, _, _⟩ :=
    central_free_diagonal_geometry hn hodd reserved hcenter
  change Y.card ≤ n - 1 at hYcard
  change Z.card ≤ n - 1 at hZcard
  have hc := actualUnusedPool_card n a reserved
  have hn2 : 7*n ≤ n*n := by nlinarith
  have hs : 1+Y.card+Z.card+1 ≤ 2*n := by omega
  have hroom : 1+Y.card+Z.card < (actualUnusedPool a reserved).card := by nlinarith
  have hYc : center ∉ Y := by simpa [center, Y] using hXY
  have hZc : center ∉ Z := by simpa [center, Z] using hXZ
  obtain ⟨b₀, b, T, U, hfixed₀, hexpect, hT, hU, hTc, hUc, hY, hZ,
    hfixed, hremain, hpos, hfirst, hsecond, hsum⟩ :=
    actual_center_and_two_full_stock_batches a reserved Y Z center hcenter hYR hZR hYZ hYc hZc hroom
  let stock := actualUnusedPool b₀ R
  have hposT : 0 < (stock \ T).card := by
    have hsub : (stock \ T) \ U ⊆ stock \ T := Finset.sdiff_subset
    have hcard := Finset.card_le_card hsub
    have hleft : 0 < ((stock \ T) \ U).card := by rw [← hremain]; exact hpos
    omega
  have hsumY := finite_population_sum b Y T hY
  have hsumZ := finite_population_sum b Z U hZ
  have hfirst' : |(∑ x ∈ T, centralPoolValue x) - (T.card : ℝ) * centralEntriesMean stock centralPoolValue| ≤
      (poolMaximum n : ℝ) / 2 := by simpa [stock, R, ← hTc, hsumY] using hfirst
  have hsecond' : |(∑ x ∈ U, centralPoolValue x) - (U.card : ℝ) * centralEntriesMean (stock \ T) centralPoolValue| ≤
      (poolMaximum n : ℝ) / 2 := by simpa [stock, R, ← hUc, hsumZ] using hsecond
  have hzbound := full_stock_second_batch_original_mean stock T U centralPoolValue (poolMaximum n) hT hU hposT hfirst' hsecond'
  have hzphys : |(∑ z ∈ Z, (entry b z : ℝ)) - (Z.card : ℝ) * centralEntriesMean stock centralPoolValue| ≤
      (poolMaximum n : ℝ) := by simpa [hsumZ, ← hUc] using hzbound
  have hmainD : mainCells n \ R = Y := by ext z; simp [R, Y, center, centralFreeMain, Finset.mem_sdiff, and_assoc, and_comm]
  have hantiD : antiCells n \ R = Z := by ext z; simp [R, Z, center, centralFreeAnti, Finset.mem_sdiff, and_assoc, and_comm]
  have hdisY : Disjoint R Y := (Finset.disjoint_union_right.mpr ⟨hYR, by simpa using hYc⟩).symm
  have hdisZ : Disjoint R Z := (Finset.disjoint_union_right.mpr ⟨hZR, by simpa using hZc⟩).symm
  have hm := full_stock_complete_line_from_batch b₀ b R Y (mainCells n) (centralEntriesMean stock centralPoolValue)
    ((poolMaximum n : ℝ)/2) hmainD hdisY hfixed hfirst
  have ha := full_stock_complete_line_from_batch b₀ b R Z (antiCells n) (centralEntriesMean stock centralPoolValue)
    (poolMaximum n) hantiD hdisZ hfixed hzphys
  have hmcenter := hexpect (mainCells n)
  have hacenter := hexpect (antiCells n)
  rw [← mainSum_real_cells] at hm
  rw [← antiSum_real_cells] at ha
  have hmt := abs_sub_le (mainSum b : ℝ)
    ((∑ z ∈ mainCells n ∩ R, (entry b₀ z : ℝ)) + ((mainCells n \ R).card : ℝ) * centralEntriesMean stock centralPoolValue)
    ((∑ z ∈ mainCells n ∩ reserved, (entry a z : ℝ)) + ((mainCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)
  have hat := abs_sub_le (antiSum b : ℝ)
    ((∑ z ∈ antiCells n ∩ R, (entry b₀ z : ℝ)) + ((antiCells n \ R).card : ℝ) * centralEntriesMean stock centralPoolValue)
    ((∑ z ∈ antiCells n ∩ reserved, (entry a z : ℝ)) + ((antiCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)
  have hpart : ({center} : Finset (Cell n)) ∪ Y ∪ Z = unreservedDiagonalCells reserved :=
    unreservedDiagonalCells_partition hn hodd reserved hcenter
  have hfinal : (reserved ∪ {center}) ∪ (Y ∪ Z) = reserved ∪ unreservedDiagonalCells reserved := by
    rw [← hpart]
    ext x
    simp only [Finset.mem_union]
    tauto
  have hdis : Disjoint reserved (unreservedDiagonalCells reserved) := by
    apply Finset.disjoint_left.mpr
    intro z hz hdiag
    exact (Finset.mem_sdiff.mp hdiag).2 hz
  have hdisCY : Disjoint ({center} : Finset (Cell n)) Y := by simpa [center, Y] using hXY
  have hdisCZ : Disjoint ({center} : Finset (Cell n)) Z := by simpa [center, Z] using hXZ
  have hcarddiag : (unreservedDiagonalCells reserved).card = 1+Y.card+Z.card := by
    rw [← hpart, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisCZ, hYZ⟩),
      Finset.card_union_of_disjoint hdisCY]
    simp
  have hcardres : (reserved ∪ unreservedDiagonalCells reserved).card = reserved.card + (1+Y.card+Z.card) := by
    rw [Finset.card_union_of_disjoint hdis, hcarddiag]
  have hbcard := actualUnusedPool_card n b (reserved ∪ unreservedDiagonalCells reserved)
  have hfinalcount : 2*n ≤ (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card := by
    rw [hcardres] at hbcard
    nlinarith
  have hdisBatch : Disjoint R (Y ∪ Z) := Finset.disjoint_union_right.mpr ⟨hdisY, hdisZ⟩
  have hmean := center_and_batches_post_mean_shift a b₀ b reserved Y Z center T U hcenter
    hfixed₀ hexpect hT hU hTc hUc hY hZ hremain hpos hsum
  rw [hfinal] at hmean
  refine ⟨b₀, b, hfixed₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz; exact (hfixed z (Finset.mem_union_left _ hz)).trans (hfixed₀ z hz)
  · change |(mainSum b : ℝ) - _| ≤ _ at hm
    change |_ - _| ≤ _ at hmcenter
    linarith
  · change |(antiSum b : ℝ) - _| ≤ _ at ha
    change |_ - _| ≤ _ at hacenter
    linarith
  · exact hfinalcount
  · exact hmean
  · intro line hlinecard hlineD
    have hsub : line ∩ (Y ∪ Z) ⊆ line ∩ unreservedDiagonalCells reserved := by
      intro z hz
      obtain ⟨hzline, hzYZ⟩ := Finset.mem_inter.mp hz
      refine Finset.mem_inter.mpr ⟨hzline, ?_⟩
      rw [← hpart]
      simp only [Finset.mem_union] at *
      tauto
    have hi := (Finset.card_le_card hsub).trans hlineD
    have hbatch := placed_full_stock_line_expectation_shift b₀ b R Y Z line
      T U hT hU hTc hUc hY hZ hdisBatch hfixed hremain hpos hsum hi
    have hcenter' := hexpect line
    have htriangle := abs_sub_le
      ((∑ z ∈ line ∩ ((reserved ∪ {center}) ∪ (Y ∪ Z)), (entry b z : ℝ)) +
        ((line \ ((reserved ∪ {center}) ∪ (Y ∪ Z))).card : ℝ) *
          centralEntriesMean (actualUnusedPool b ((reserved ∪ {center}) ∪ (Y ∪ Z))) centralPoolValue)
      ((∑ z ∈ line ∩ (reserved ∪ {center}), (entry b₀ z : ℝ)) +
        ((line \ (reserved ∪ {center})).card : ℝ) *
          centralEntriesMean (actualUnusedPool b₀ (reserved ∪ {center})) centralPoolValue)
      ((∑ z ∈ line ∩ reserved, (entry a z : ℝ)) +
        ((line \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)
    have hk : (line \ (reserved ∪ unreservedDiagonalCells reserved)).card ≤ n :=
      (Finset.card_le_card Finset.sdiff_subset).trans hlinecard
    have hX : 0 ≤ (poolMaximum n : ℝ) := by positivity
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hkreal : ((line \ (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) ≤ n := by exact_mod_cast hk
    have hNreal : 2*(n : ℝ) ≤ (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card := by exact_mod_cast hfinalcount
    have hscalar := full_stock_three_x_arithmetic (poolMaximum n) n
      (line \ (reserved ∪ unreservedDiagonalCells reserved)).card
      (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card hX hnreal hkreal hNreal
    rw [hfinal] at htriangle hbatch
    dsimp only [R] at hbatch
    linarith


/-- Compatibility wrapper retaining the original diagonal-witness interface. -/
theorem odd_full_stock_integrated_diagonal_witness {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (reserved : Finset (Cell n)) (hn7 : 7 ≤ n) (hodd : Odd n)
    (hcenter : centralCell n (by omega) ∉ reserved)
    (hreserve : 4 * reserved.card ≤ n*n) :
    ∃ b : Cell n ≃ Fin (n*n), (∀ z ∈ reserved, entry b z = entry a z) ∧
      |(mainSum b : ℝ) - ((∑ z ∈ mainCells n ∩ reserved, (entry a z : ℝ)) +
        ((mainCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (poolMaximum n : ℝ) ∧
      |(antiSum b : ℝ) - ((∑ z ∈ antiCells n ∩ reserved, (entry a z : ℝ)) +
        ((antiCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (3/2 : ℝ) * poolMaximum n ∧
      2*n ≤ (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card ∧
      ∀ line : Finset (Cell n), line.card ≤ n → (line ∩ unreservedDiagonalCells reserved).card ≤ 2 →
        |((∑ z ∈ line ∩ (reserved ∪ unreservedDiagonalCells reserved), (entry b z : ℝ)) +
            ((line \ (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) *
              centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue) -
          ((∑ z ∈ line ∩ reserved, (entry a z : ℝ)) +
            ((line \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          3 * (poolMaximum n : ℝ) := by
  obtain ⟨b₀, b, _, hfixed, hmain, hanti, hstock, _, hlines⟩ :=
    odd_full_stock_integrated_diagonal_witness_with_mean a reserved hn7 hodd hcenter hreserve
  exact ⟨b, hfixed, hmain, hanti, hstock, hlines⟩

end
end Sude
