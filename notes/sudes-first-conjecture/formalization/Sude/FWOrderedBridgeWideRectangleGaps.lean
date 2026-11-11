import Sude.FWThetaFamilyWitness
import Sude.FWControllerStageReindex

/-! Signed bridge and wide rectangle gaps on one supplied ordered family.
The rectangle choice is arbitrary. No grid, CY transfer or prime claim is
asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Both correctly oriented bridge pairs use the destination block's signed
gap; the second row is oriented from corner 3 to corner 2. -/
theorem fw_ordered_bridge_rectangle_gaps {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice) (j : Fin 5) (rect : Fin (4*6)) :
    let label := bridgeDiagonalRectangle f.hrect (finProdFinEquiv (j,rect))
    let block : Fin (3*(n+8)) := Fin.castLE (by omega : 4*6 ≤ 3*(n+8)) rect
    entry f.ordered (packedRectangleCorner f.hs choice (label,1)) =
      entry f.ordered (packedRectangleCorner f.hs choice (label,0)) + f.gapb j block ∧
    entry f.ordered (packedRectangleCorner f.hs choice (label,2)) =
      entry f.ordered (packedRectangleCorner f.hs choice (label,3)) + f.gapb j block := by
  dsimp only
  let block : Fin (3*(n+8)) := Fin.castLE (by omega : 4*6 ≤ 3*(n+8)) rect
  have hcell (pair : Fin 2) (side : Bool) :
      fwBridgePhysicalDoubleCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc ((j,block,pair),side) =
        packedRectangleCorner f.hs choice
          (bridgeDiagonalRectangle f.hrect (finProdFinEquiv (j,rect)), prefixPairCorner pair side) := by
    have h := fw_bridge_reindexed_diagonal_cell f.hrect f.hs choice f.br f.bc f.hbr f.hbc j rect pair side
    rw [fwPrefixToControllerPair_diagonal] at h
    exact h
  have h₀ := f.hinvoiceb j block 0
  have h₁ := f.hinvoiceb j block 1
  rw [hcell 0 true, hcell 0 false] at h₀
  rw [hcell 1 true, hcell 1 false] at h₁
  exact ⟨by simpa [prefixPairCorner] using h₀, by simpa [prefixPairCorner] using h₁⟩

/-- Both correctly oriented wide pairs use the destination block's signed
gap; the second row is oriented from corner 3 to corner 2. -/
theorem fw_ordered_wide_rectangle_gaps {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice) (j : Fin (3*(n/450))) (rect : Fin (4*6)) :
    let label := fwWideRectangle f.hwide (finProdFinEquiv (j,rect))
    let block : Fin (3*(n+8)) := Fin.castLE (by omega : 4*6 ≤ 3*(n+8)) rect
    entry f.ordered (packedRectangleCorner f.hs choice (label,1)) =
      entry f.ordered (packedRectangleCorner f.hs choice (label,0)) + f.gapw j block ∧
    entry f.ordered (packedRectangleCorner f.hs choice (label,2)) =
      entry f.ordered (packedRectangleCorner f.hs choice (label,3)) + f.gapw j block := by
  dsimp only
  let block : Fin (3*(n+8)) := Fin.castLE (by omega : 4*6 ≤ 3*(n+8)) rect
  have hcell (pair : Fin 2) (side : Bool) :
      fwWidePhysicalDoubleCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc ((j,block,pair),side) =
        packedRectangleCorner f.hs choice
          (fwWideRectangle f.hwide (finProdFinEquiv (j,rect)), prefixPairCorner pair side) := by
    have h := fw_wide_reindexed_diagonal_cell f.hwide f.hs choice f.wr f.wc f.hwr f.hwc j rect pair side
    rw [fwPrefixToControllerPair_diagonal] at h
    exact h
  have h₀ := f.hinvoicew j block 0
  have h₁ := f.hinvoicew j block 1
  rw [hcell 0 true, hcell 0 false] at h₀
  rw [hcell 1 true, hcell 1 false] at h₁
  exact ⟨by simpa [prefixPairCorner] using h₀, by simpa [prefixPairCorner] using h₁⟩

end
end Sude
