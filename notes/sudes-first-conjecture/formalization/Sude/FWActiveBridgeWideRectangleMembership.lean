import Sude.FWControllerStageReindex
import Sude.FWActiveRectangleLabels
import Sude.ActiveRectangleLineCounts

/-! The bridge and wide diagonal pair endpoints are corners of the actual
active FW rectangle labels. No numerical bound or allocation is asserted. -/
namespace Sude
noncomputable section

/-- Each controller-reindexed bridge rectangle endpoint belongs to the
active-rectangle support for the same FW layout. -/
theorem fw_bridge_diagonal_cell_mem_active_rectangle {n P : ℕ} (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc : List (LayerPacking.Layer n)) (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (j : Fin 5) (rect : Fin (4 * 6)) (pair : Fin 2) (side : Bool) :
    fwBridgePhysicalPairCells hrect hs choice br bc hbr hbc
      ((j, fwPrefixToControllerPair n (prefixDiagonalPairIndex
        (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair))), side) ∈
      activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP) := by
  classical
  rw [fw_bridge_reindexed_diagonal_cell]
  apply Finset.mem_image.mpr
  refine ⟨(bridgeDiagonalRectangle hrect (finProdFinEquiv (j,rect)), prefixPairCorner pair side), ?_, rfl⟩
  apply Finset.mem_product.mpr
  refine ⟨(fw_active_rectangle_label_mem_iff n P hP _).2 ?_, Finset.mem_univ _⟩
  have h := (finProdFinEquiv (j,rect) : Fin (5 * (4 * 6))).isLt
  simp only [bridgeDiagonalRectangle, Fin.val_castLE, fwActiveRectangleCount]
  omega

/-- Each controller-reindexed wide rectangle endpoint belongs to the same
active-rectangle support. -/
theorem fw_wide_diagonal_cell_mem_active_rectangle {n P : ℕ} (hP : P ≤ 238)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (wr wc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (rect : Fin (4 * 6)) (pair : Fin 2) (side : Bool) :
    fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc
      ((j, fwPrefixToControllerPair n (prefixDiagonalPairIndex
        (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair))), side) ∈
      activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP) := by
  classical
  rw [fw_wide_reindexed_diagonal_cell]
  apply Finset.mem_image.mpr
  refine ⟨(fwWideRectangle hwide (finProdFinEquiv (j,rect)), prefixPairCorner pair side), ?_, rfl⟩
  apply Finset.mem_product.mpr
  refine ⟨(fw_active_rectangle_label_mem_iff n P hP _).2 ?_, Finset.mem_univ _⟩
  have h := (finProdFinEquiv (j,rect) : Fin ((3 * (n / 450)) * (4 * 6))).isLt
  simp only [fwWideRectangle, fwActiveRectangleCount]
  omega

end
end Sude
