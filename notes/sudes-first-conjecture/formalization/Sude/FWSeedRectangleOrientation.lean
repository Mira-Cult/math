import Sude.FWSeedOrientationPartition

/-! In the actual offset seed geometry, subtracting the matched ordinary
network orientation from all selected-pair orientations leaves exactly the
rectangle-pair orientations. No rectangle sum is assumed to vanish. -/
namespace Sude
noncomputable section
open scoped BigOperators
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

theorem fw_seed_row_remaining_orientation {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (br sr wr gr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3) (r : Fin n) (gap : ℝ) :
    let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let orient := physicalPairLineOrientation cells (fun x => x.1 = r)
    let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
    (∑ p : Fin 16 × Fin (6 * (n + 8)), orient p * (gap / 2)) -
        (gap / 2) * ∑ t ∈ fwSeedJointPairImage br sr wr gr hsr,
          orient (fwSeedJointToOrdinaryIndex br sr wr gr hsr 0 t) =
      (gap / 2) * ∑ j : Fin 16, ∑ x : Fin (4 * 6) × Fin 2,
        orient (j, prefixDiagonalPairIndex hdiag x) := by
  classical
  dsimp only
  rw [← Finset.sum_mul]
  have h := fw_seed_row_orientation_split hseed hs choice br sr wr gr sc hsr hsc r
  dsimp only at h
  rw [h]
  ring

theorem fw_seed_column_remaining_orientation {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr bc sc wc gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3) (c : Fin n) (gap : ℝ) :
    let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let orient := physicalPairLineOrientation cells (fun x => x.2 = c)
    let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
    (∑ p : Fin 16 × Fin (6 * (n + 8)), orient p * (gap / 2)) -
        (gap / 2) * ∑ t ∈ fwSeedJointPairImage bc sc wc gc hsc,
          orient (fwSeedJointToOrdinaryIndex bc sc wc gc hsc 1 t) =
      (gap / 2) * ∑ j : Fin 16, ∑ rect : Fin (4 * 6), ∑ pair : Fin 2,
        orient (j, prefixDiagonalPairIndex hdiag (rect,pair)) := by
  classical
  dsimp only
  rw [← Finset.sum_mul]
  have h := fw_seed_column_orientation_split hseed hs choice sr bc sc wc gc hsr hsc c
  dsimp only at h
  rw [h]
  ring

end
end Sude
