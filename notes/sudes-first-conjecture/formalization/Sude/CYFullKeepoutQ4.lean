import Sude.CYFullKeepoutRow
import Sude.CYFullKeepoutColumn
import Sude.CYFullKeepoutLayers

namespace Sude
noncomputable section

theorem cy_full_cy_q4_and_center {L n : ℕ}
    (hs : 2*L+1 ≤ n) (hL : 3 ≤ L) (hn : 0<n) (hodd : Odd n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols) :
    let ρ := 2 * (rows.length + cols.length)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)
    let final := full ∪ unreservedDiagonalCells full
    ((Finset.univ : Finset (Fin n)).filter (fun i => (LayerPacking.rowUsed final i).card = ρ+4)).card = L ∧
    ((Finset.univ : Finset (Fin n)).filter (fun i => (LayerPacking.colUsed final i).card = ρ+4)).card = L ∧
    (LayerPacking.rowUsed final (centerIndex n hn)).card = ρ+1 ∧
    (LayerPacking.colUsed final (centerIndex n hn)).card = ρ+1 := by
  classical
  dsimp only
  let rect := packedRectangleSupport hs choice
  let diag := mainCells n ∪ antiCells n
  let ρ := 2 * (rows.length + cols.length)
  let full := rect ∪ LayerPacking.layersSupport rows ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols)
  let final := full ∪ unreservedDiagonalCells full
  have hb := cy_rectangle_diagonal_layers_load hs choice rows cols hrows hcols
  change (∀ i, (LayerPacking.rowUsed final i).card = (LayerPacking.rowUsed (rect ∪ diag) i).card + ρ) ∧
    (∀ i, (LayerPacking.colUsed final i).card = (LayerPacking.colUsed (rect ∪ diag) i).card + ρ) at hb
  have hr : ((Finset.univ : Finset (Fin n)).filter (fun i => (LayerPacking.rowUsed final i).card = ρ+4)) =
      (Finset.univ.filter fun i => (LayerPacking.rowUsed (rect ∪ diag) i).card = 4) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hb.1 i]
    omega
  have hc : ((Finset.univ : Finset (Fin n)).filter (fun i => (LayerPacking.colUsed final i).card = ρ+4)) =
      (Finset.univ.filter fun i => (LayerPacking.colUsed (rect ∪ diag) i).card = 4) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hb.2 i]
    omega
  change ((Finset.univ : Finset (Fin n)).filter (fun i => (LayerPacking.rowUsed final i).card = ρ+4)).card = L ∧
    ((Finset.univ : Finset (Fin n)).filter (fun i => (LayerPacking.colUsed final i).card = ρ+4)).card = L ∧
    (LayerPacking.rowUsed final (centerIndex n hn)).card = ρ+1 ∧
    (LayerPacking.colUsed final (centerIndex n hn)).card = ρ+1
  have hcenter := cy_rect_diag_center_lines hs hn hodd choice
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hr]; exact cy_row_q4_card hs hL hn hodd choice
  · rw [hc]; exact cy_column_q4_card hs hL choice
  · rw [hb.1]; dsimp [rect, diag]; rw [hcenter.1]; omega
  · rw [hb.2]; dsimp [rect, diag]; rw [hcenter.2]; omega
end
end Sude
