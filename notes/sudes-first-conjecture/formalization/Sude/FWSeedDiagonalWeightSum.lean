import Sude.FWSeedOffsetActualDiagonal

/-! Unsquared physical seed diagonal incidence counts for each stage. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

theorem fw_seed_existing_main_weight_sum {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows sr)
    (packedCols : LayerPacking.PackedLayers reservedCols sc) (j : Fin 16) :
    ∑ q : Fin (6 * (n + 8)),
      physicalPairLineWeight (fwSeedExistingPairCells hseed hs
        (fwBridgeSeedRectangleChoice hrect hseed otherChoice) sr sc hsr hsc)
        (fun c => c ∈ mainCells n) (j, q) = 12 := by
  classical
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixStagePairSlot hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  let choice := fwBridgeSeedRectangleChoice hrect hseed otherChoice
  let w := fun q : Fin (6 * (n + 8)) => physicalPairLineWeight
    (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) (fun c => c ∈ mainCells n) (j, q)
  have hpoint (tag : PrefixStagePair 6 3 n) : w (e tag) = (w (e tag)) ^ 2 := by
    change physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
      (fun c => c ∈ mainCells n) (j, prefixStagePairSlot hfit hdiag tag) =
      (physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun c => c ∈ mainCells n) (j, prefixStagePairSlot hfit hdiag tag)) ^ 2
    rw [fw_seed_existing_main_weight_at_label hseed hs choice sr sc hsr hsc
      reservedRows reservedCols packedRows packedCols]
    cases tag with
    | inl x =>
      rcases x with ⟨rect, pair⟩
      simp only [fwSeedOffsetDiagonalIncidence, rectanglePairWeight_main hs hL]
      split_ifs <;> norm_num
    | inr x => simp [fwSeedOffsetDiagonalIncidence]
  calc
    ∑ q, w q = ∑ tag : PrefixStagePair 6 3 n, w (e tag) := (e.sum_comp w).symm
    _ = ∑ tag : PrefixStagePair 6 3 n, (w (e tag)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro tag _
      exact hpoint tag
    _ = ∑ q, (w q) ^ 2 := e.sum_comp (fun q => (w q) ^ 2)
    _ = 12 := fw_seed_existing_main_squared_sum hrect hseed hs hL otherChoice sr sc hsr hsc
      reservedRows reservedCols packedRows packedCols j

theorem fw_seed_existing_anti_weight_sum {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows sr)
    (packedCols : LayerPacking.PackedLayers reservedCols sc) (j : Fin 16) :
    ∑ q : Fin (6 * (n + 8)),
      physicalPairLineWeight (fwSeedExistingPairCells hseed hs
        (fwBridgeSeedRectangleChoice hrect hseed otherChoice) sr sc hsr hsc)
        (fun c => c ∈ antiCells n) (j, q) = 12 := by
  classical
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixStagePairSlot hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  let choice := fwBridgeSeedRectangleChoice hrect hseed otherChoice
  let w := fun q : Fin (6 * (n + 8)) => physicalPairLineWeight
    (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) (fun c => c ∈ antiCells n) (j, q)
  have hpoint (tag : PrefixStagePair 6 3 n) : w (e tag) = (w (e tag)) ^ 2 := by
    change physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
      (fun c => c ∈ antiCells n) (j, prefixStagePairSlot hfit hdiag tag) =
      (physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun c => c ∈ antiCells n) (j, prefixStagePairSlot hfit hdiag tag)) ^ 2
    rw [fw_seed_existing_anti_weight_at_label hseed hs choice sr sc hsr hsc
      reservedRows reservedCols packedRows packedCols]
    cases tag with
    | inl x =>
      rcases x with ⟨rect, pair⟩
      simp only [fwSeedOffsetDiagonalIncidence, rectanglePairWeight_anti hs hL]
      split_ifs <;> norm_num
    | inr x => simp [fwSeedOffsetDiagonalIncidence]
  calc
    ∑ q, w q = ∑ tag : PrefixStagePair 6 3 n, w (e tag) := (e.sum_comp w).symm
    _ = ∑ tag : PrefixStagePair 6 3 n, (w (e tag)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro tag _
      exact hpoint tag
    _ = ∑ q, (w q) ^ 2 := e.sum_comp (fun q => (w q) ^ 2)
    _ = 12 := fw_seed_existing_anti_squared_sum hrect hseed hs hL otherChoice sr sc hsr hsc
      reservedRows reservedCols packedRows packedCols j

end
end Sude
