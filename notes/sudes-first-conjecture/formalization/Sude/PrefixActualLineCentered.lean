import Sude.PhysicalLineCenteredIdentity
import Sude.PhysicalAllLineWeights
import Sude.PermutedSeedMidpoints
import Sude.PrefixPlacementInjective

/-! Relate every physical prefix line to the source midpoint variable. -/
namespace Sude
noncomputable section

/-- For each labelled line, actual selected prefix entries equal the
centered without-replacement variable plus explicit means and half-gaps.
This identity concerns selected cells; completing the other cells remains
an independent obligation. -/
theorem prefix_actual_line_eq_centered {n r P Q gap d layers L : ℕ}
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
        (prefixPhysicalInput hfit hdiag x)).val)
    (l : Fin ((n + n) + 2)) :
    let cells := prefixPairCells hfit hdiag hexact hrect hs (bridgeDiagonalChoice hrect otherChoice)
      rows cols hrows hcols
    let weights := physicalAllLineWeights hfit hdiag hrect hs otherChoice rows cols hrows hcols
    let values := retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept
    (∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ physicalAllLineCells l), (entry a c : ℝ)) =
      stageLineCentered (physicalAllLineSlots hfit hdiag) weights values l ω +
      (∑ j, ((∑ q, weights l j q) * ((∑ q, values j q) / (Q : ℝ)))) +
      ∑ p, physicalPairLineOrientation cells (fun c => c ∈ physicalAllLineCells l) p * ((gap : ℝ) / 2) := by
  classical
  dsimp only
  let cells := prefixPairCells hfit hdiag hexact hrect hs (bridgeDiagonalChoice hrect otherChoice)
    rows cols hrows hcols
  let values := permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
  have hp : Function.Injective (prefixPhysicalCells hrect hs (bridgeDiagonalChoice hrect otherChoice)
      rows cols hrows hcols) :=
    prefixPhysicalCells_injective_of_placement hfit hdiag hrect hs _ rows cols hrows hcols a values
      (permutedRetainedSeedValues_injective candidates r P Q gap hcard kept hsub hkept initial hav hinj ω) hplaced
  have hc : Function.Injective cells :=
    prefixPairCells_injective hfit hdiag hexact hrect hs _ rows cols hrows hcols hp
  have he := physicalPair_line_sum_eq_centered hQ cells hc
    (fun l c => c ∈ physicalAllLineCells l) a
    (physicalAllLineWeights hfit hdiag hrect hs otherChoice rows cols hrows hcols)
    (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept) ω (gap : ℝ)
    (physicalAllLineWeight_eq_pair_incidence hfit hdiag hexact hrect hs otherChoice
      rows cols hrows hcols reservedRows reservedCols packedRows packedCols) ?_ ?_ l
  · have hslots : physicalAllLineSlots (P := P) hfit hdiag =
        (fun _ _ => Finset.univ) := by
      funext l j
      exact physicalPrefixSlots_eq_univ hfit hdiag hexact
    rw [hslots]
    exact he
  · intro j q
    rw [prefixPairCells_entry hfit hdiag hexact hrect hs _ rows cols hrows hcols a values hplaced,
      prefixPairCells_entry hfit hdiag hexact hrect hs _ rows cols hrows hcols a values hplaced]
    exact permutedRetainedSeed_pair_midpoint candidates r P Q gap hcard kept hsub hkept initial hav ω j q
  · intro j q
    rw [prefixPairCells_entry hfit hdiag hexact hrect hs _ rows cols hrows hcols a values hplaced,
      prefixPairCells_entry hfit hdiag hexact hrect hs _ rows cols hrows hcols a values hplaced]
    have h := permutedRetainedSeedValues_gap candidates r P Q gap hcard kept hsub hkept initial hav ω j q
    have hh : ((values ((j, q), true)).val : ℝ) = (values ((j, q), false)).val + gap := by exact_mod_cast h
    linarith

end
end Sude
