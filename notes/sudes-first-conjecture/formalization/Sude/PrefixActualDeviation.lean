import Sude.PrefixActualLineCentered

/-! Transfer the all-line midpoint bound to the installed prime-pair cells. -/
namespace Sude
noncomputable section

/-- A simultaneous physical midpoint bound controls the selected contribution
of the actually installed retained prime pairs on every labelled line, after
subtracting the exact stage means and signed gap. It says nothing yet about
unselected cells, targets, or primality of a completed line. -/
theorem prefix_actual_line_deviation_le {n r P Q gap d layers L : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard))
    (hQ : 0 < Q) (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q)
    (hdiag : (4 * d) * 2 ≤ Q) (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (otherChoice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows rows)
    (packedCols : LayerPacking.PackedLayers reservedCols cols)
    (ω : Fin P → Equiv.Perm (Fin Q)) (a : Cell n ≃ Fin (n * n))
    (hplaced : ∀ x, entry a (prefixPhysicalCells hrect hs (bridgeDiagonalChoice hrect otherChoice)
      rows cols hrows hcols x) =
      (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
        (prefixPhysicalInput hfit hdiag x)).val) (B : ℝ)
    (hbound : ∀ l, |stageLineCentered (physicalAllLineSlots hfit hdiag)
      (physicalAllLineWeights hfit hdiag hrect hs otherChoice rows cols hrows hcols)
      (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept) l ω| ≤ B) :
    let cells := prefixPairCells hfit hdiag hexact hrect hs (bridgeDiagonalChoice hrect otherChoice)
      rows cols hrows hcols
    let weights := physicalAllLineWeights hfit hdiag hrect hs otherChoice rows cols hrows hcols
    let values := retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept
    ∀ l, |(∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ physicalAllLineCells l), (entry a c : ℝ)) -
      (∑ j, ((∑ q, weights l j q) * ((∑ q, values j q) / (Q : ℝ)))) -
      (∑ p, physicalPairLineOrientation cells (fun c => c ∈ physicalAllLineCells l) p * ((gap : ℝ) / 2))| ≤ B := by
  classical
  dsimp only
  intro l
  have h := prefix_actual_line_eq_centered candidates hcard kept hsub hkept initial hav hinj hQ
    hfit hdiag hexact hrect hs otherChoice rows cols hrows hcols reservedRows reservedCols
    packedRows packedCols ω a hplaced l
  have heq : (∑ c ∈ (Finset.univ.image (prefixPairCells hfit hdiag hexact hrect hs
        (bridgeDiagonalChoice hrect otherChoice) rows cols hrows hcols)).filter
        (fun c => c ∈ physicalAllLineCells l), (entry a c : ℝ)) -
      (∑ j, ((∑ q, physicalAllLineWeights hfit hdiag hrect hs otherChoice rows cols hrows hcols l j q) *
        ((∑ q, retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j q) / (Q : ℝ)))) -
      (∑ p, physicalPairLineOrientation (prefixPairCells hfit hdiag hexact hrect hs
        (bridgeDiagonalChoice hrect otherChoice) rows cols hrows hcols)
        (fun c => c ∈ physicalAllLineCells l) p * ((gap : ℝ) / 2)) =
      stageLineCentered (physicalAllLineSlots hfit hdiag)
        (physicalAllLineWeights hfit hdiag hrect hs otherChoice rows cols hrows hcols)
        (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept) l ω := by linarith
  rw [heq]
  exact hbound l

end
end Sude
