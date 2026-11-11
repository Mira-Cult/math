import Sude.FWSeedNetworkMatching
import Sude.PhysicalPairLineSum

/-! Perpendicular ordinary seed pairs contribute no signed half-gap on a
row or column. Seed rectangle orientations remain separate. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- A column-network ordinary seed pair is horizontal in the original
square, so both endpoints meet the same row or neither does. -/
theorem fw_seed_column_pair_row_orientation_zero {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (j : Fin 16) (k : Fin 3) (e r : Fin n) :
    physicalPairLineOrientation (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
      (fun x => x.1 = r)
      (j, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (1,k,e)) = 0 := by
  classical
  unfold physicalPairLineOrientation
  rw [fw_seed_existing_column_cell, fw_seed_existing_column_cell]
  simp [LayerPacking.layerCell]

/-- A row-network ordinary seed pair is vertical in the original square,
so both endpoints meet the same column or neither does. -/
theorem fw_seed_row_pair_column_orientation_zero {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (j : Fin 16) (k : Fin 3) (e c : Fin n) :
    physicalPairLineOrientation (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
      (fun x => x.2 = c)
      (j, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (0,k,e)) = 0 := by
  classical
  unfold physicalPairLineOrientation
  rw [fw_seed_existing_row_cell, fw_seed_existing_row_cell]
  simp [LayerPacking.layerCell]

end
end Sude
