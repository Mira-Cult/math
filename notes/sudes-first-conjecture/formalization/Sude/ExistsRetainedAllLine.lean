import Sude.FixedRetainedSourceWidth
import Sude.FixedSeedLayoutExistence

/-! Select packed geometry before randomization and use source width bounds. -/
namespace Sude
noncomputable section

/-- From actual selected-pair supply, source width estimates, and explicit
physical capacity, construct packed geometry and one all-line midpoint
allocation. Line-target identities and controller hypotheses remain separate. -/
theorem exists_retained_all_line_source_allocation {n r P Q gap d layers L Bload : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard))
    (hQ : 0 < Q) (hd : d = 2 * layers) (z : ℝ)
    (hmax : ∀ i ∈ kept, sortedSeedReal candidates r Q hcard (i * Q + (Q - 1)) -
      sortedSeedReal candidates r Q hcard (i * Q) ≤ z) (V : ℝ)
    (hsource : 3 * (d : ℝ) * (∑ i ∈ kept,
      (sortedSeedReal candidates r Q hcard (i * Q + (Q - 1)) -
       sortedSeedReal candidates r Q hcard (i * Q)) ^ 2) + 4 * z ^ 2 ≤ V)
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrlen : rowPerms.length = P * layers) (hclen : colPerms.length = P * layers)
    (hrderange : ∀ π ∈ rowPerms, ∀ i, π i ≠ i)
    (hcderange : ∀ π ∈ colPerms, ∀ i, π i ≠ i)
    (base : Finset (Cell n)) (hrload : ∀ i, (LayerPacking.rowUsed base i).card ≤ Bload)
    (hcload : ∀ i, (LayerPacking.colUsed base i).card ≤ Bload)
    (hcapacity : 4 * ((Bload + 2) + 2 * rowPerms.length + 2 * colPerms.length) + 8 < n)
    (a : Cell n ≃ Fin (n * n)) (hbase : ∀ c ∈ base, entry a c ∈ initial)
    (hfree : ∀ x : Fin (P * (4 * d)) × Fin 4,
      packedRectangleCorner hs (bridgeDiagonalChoice hrect otherChoice) (Fin.castLE hrect x.1, x.2) ∉ base) :
    ∃ (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = rowPerms.length)
      (hcols : cols.length = colPerms.length) (ω : Fin P → Equiv.Perm (Fin Q))
      (b : Cell n ≃ Fin (n * n)),
      rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
      LayerPacking.PackedLayers (base ∪ allocatedBridgeRectangleSupport hrect hs (bridgeDiagonalChoice hrect otherChoice)) rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        ((base ∪ allocatedBridgeRectangleSupport hrect hs (bridgeDiagonalChoice hrect otherChoice)) ∪
          LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows) (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      (∀ l, |stageLineCentered (physicalAllLineSlots hfit hdiag)
        (physicalAllLineWeights hfit hdiag hrect hs otherChoice rows cols (hrows.trans hrlen) (hcols.trans hclen))
        (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept) l ω| ≤
        Real.sqrt (V * Real.log (4 * (((n + n) + 2 : ℕ) : ℝ)) / 2)) ∧
      (∀ x, entry b (prefixPhysicalCells hrect hs (bridgeDiagonalChoice hrect otherChoice)
          rows cols (hrows.trans hrlen) (hcols.trans hclen) x) =
        (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
          (prefixPhysicalInput hfit hdiag x)).val) ∧
      (∀ c ∈ base, entry b c = entry a c) ∧
      Finset.univ.image (fun x => entry b (prefixPhysicalCells hrect hs (bridgeDiagonalChoice hrect otherChoice)
        rows cols (hrows.trans hrlen) (hcols.trans hclen) x)) =
          retainedSeedEndpoints candidates r Q gap hcard kept hsub := by
  obtain ⟨rows, cols, hrows, hcols, hrmap, hcmap, hrpack, hcpack, hdis, hcell, hcellfree, _⟩ :=
    exists_fixed_seed_layout candidates hcard kept hsub hkept initial hav hinj hfit hdiag hexact
      hrect hs (bridgeDiagonalChoice hrect otherChoice) rowPerms colPerms hrlen hclen hrderange hcderange
      base hrload hcload hcapacity a hbase hfree
  obtain ⟨ω, b, hbound, hplaced, hfixed, hused⟩ := fixed_retained_all_line_source_width
    candidates hcard kept hsub hkept initial hav hinj hQ hd z hmax V hsource hfit hdiag hexact
    hrect hs hL otherChoice rows cols (hrows.trans hrlen) (hcols.trans hclen) _ _ hrpack hcpack
    a base hbase hcell hcellfree
  exact ⟨rows, cols, hrows, hcols, ω, b, hrmap, hcmap, hrpack, hcpack, hdis, hbound, hplaced, hfixed, hused⟩

end
end Sude
