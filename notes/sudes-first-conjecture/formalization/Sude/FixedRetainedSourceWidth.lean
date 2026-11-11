import Sude.FixedRetainedAllLine
import Sude.RetainedWidthInvoice

/-! Source selected-group widths discharge the physical stage width cap. -/
namespace Sude
noncomputable section

theorem fixed_retained_all_line_source_width {n r P Q gap d layers L : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard))
    (hQ : 0 < Q) (hd : d = 2 * layers) (z : ℝ)
    (hmax : ∀ i ∈ kept, sortedSeedReal candidates r Q hcard (i * Q + (Q - 1)) -
      sortedSeedReal candidates r Q hcard (i * Q) ≤ z) (B : ℝ)
    (hsource : 3 * (d : ℝ) * (∑ i ∈ kept,
      (sortedSeedReal candidates r Q hcard (i * Q + (Q - 1)) -
       sortedSeedReal candidates r Q hcard (i * Q)) ^ 2) + 4 * z ^ 2 ≤ B)
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hrows : rows.length = P * layers) (hcols : cols.length = P * layers)
    (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows rows)
    (packedCols : LayerPacking.PackedLayers reservedCols cols)
    (a : Cell n ≃ Fin (n * n)) (base : Finset (Cell n))
    (hbase : ∀ c ∈ base, entry a c ∈ initial)
    (hcells : Function.Injective (prefixPhysicalCells hrect hs (bridgeDiagonalChoice hrect otherChoice) rows cols hrows hcols))
    (hfree : ∀ x, prefixPhysicalCells hrect hs (bridgeDiagonalChoice hrect otherChoice) rows cols hrows hcols x ∉ base) :
    ∃ ω : Fin P → Equiv.Perm (Fin Q), ∃ b : Cell n ≃ Fin (n * n),
      (∀ l, |stageLineCentered (physicalAllLineSlots hfit hdiag)
        (physicalAllLineWeights hfit hdiag hrect hs otherChoice rows cols hrows hcols)
        (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept) l ω| ≤
        Real.sqrt (B * Real.log (4 * (((n + n) + 2 : ℕ) : ℝ)) / 2)) ∧
      (∀ x, entry b (prefixPhysicalCells hrect hs (bridgeDiagonalChoice hrect otherChoice) rows cols hrows hcols x) =
        (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
          (prefixPhysicalInput hfit hdiag x)).val) ∧
      (∀ c ∈ base, entry b c = entry a c) ∧
      Finset.univ.image (fun x => entry b
        (prefixPhysicalCells hrect hs (bridgeDiagonalChoice hrect otherChoice) rows cols hrows hcols x)) =
          retainedSeedEndpoints candidates r Q gap hcard kept hsub := by
  have hwidth := retainedStage_midpoint_width_sq_le candidates r P Q gap hcard kept hsub hkept
    initial hav hQ z hmax
  obtain ⟨ω, b, hbound, hb, hfixed, hused⟩ := fixed_retained_all_line_allocation
    candidates hcard kept hsub hkept initial hav hinj hQ hd z hwidth hfit hdiag hexact hrect hs hL otherChoice
    rows cols hrows hcols reservedRows reservedCols packedRows packedCols a base hbase hcells hfree
  have hV : 3 * (d : ℝ) * (∑ j : Fin P,
      (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨Q - 1, by omega⟩ -
       retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨0, hQ⟩) ^ 2) + 4 * z ^ 2 ≤ B := by
    rw [retainedStage_midpoint_width_sq_sum candidates r P Q gap hcard kept hsub hkept hQ]
    exact hsource
  have hlog : 0 ≤ Real.log (4 * (((n + n) + 2 : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    push_cast
    linarith
  refine ⟨ω, b, ?_, hb, hfixed, hused⟩
  intro l
  apply le_trans (hbound l)
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hV hlog) (by norm_num)

end
end Sude
