import Sude.FWWideSignedGapSlots
import Sude.FWGrowthRectangleChoice
import Sude.FWPhysicalDoubleBlockCells
import Sude.ActiveRectangleDiagonalGeometry

/-! The balanced wide diagonal cells are pair-zero false endpoints. Their
centered contribution is negative one half the corresponding signed gap.
This does not bound uncentered diagonal values or spare contributions. -/
namespace Sude
noncomputable section

theorem fw_wide_balanced_physical_centered_gap {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (other : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (a : Cell n ≃ Fin (n*n))
    (π : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (gap : Fin (3 * (n / 450)) → Fin (3 * (n + 8)) → ℝ)
    (hgap : ∀ j b, (entry a (fwWidePhysicalDoubleCells hwide hs
      (fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth other) rows cols hr hc ((j,b,0),true)) : ℝ) =
      (entry a (fwWidePhysicalDoubleCells hwide hs
      (fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth other) rows cols hr hc ((j,b,0),false)) : ℝ) + gap j (π j b)) :
    let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth other
    let label := fun j side r => fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r))
    (∀ j (side : Bool) r, (if side = true then packedRectangleCorner hs choice (label j side r,0) ∈ mainCells n
      else packedRectangleCorner hs choice (label j side r,0) ∈ antiCells n)) ∧
    (∀ j side, (∑ r : Fin 12,
       ((entry a (packedRectangleCorner hs choice (label j side r,0)) : ℝ) -
        ((entry a (packedRectangleCorner hs choice (label j side r,0)) : ℝ) +
         (entry a (packedRectangleCorner hs choice (label j side r,1)) : ℝ))/2)) =
       -(1/2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n side, gap j (π j b)) := by
  classical
  dsimp only
  let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth other
  have hchoice : ∀ j side r, choice (fwWideRectangle hwide
      (finProdFinEquiv (j, fwWideSignedGapRectangle side r))) = side := by
    intro j side r
    dsimp only [choice]
    rw [fwBridgeSeedWideGrowthChoice_wide]
    cases side <;> simp [fwWideSignedGapRectangle] <;> have := r.isLt <;> omega
  constructor
  · intro j side r
    have h := hchoice j side r
    cases side
    · simpa [packedRectangleCorner] using ((RectanglePacking.designated_corner_geometry hs choice _).2 h).1
    · simpa [packedRectangleCorner] using ((RectanglePacking.designated_corner_geometry hs choice _).1 h).1
  · intro j side
    have hp : ∀ r : Fin 12,
        (entry a (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j,fwWideSignedGapRectangle side r)),1)) : ℝ) =
        (entry a (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j,fwWideSignedGapRectangle side r)),0)) : ℝ) +
        gap j (π j (fwWideSignedGapSlot n side r)) := by
      intro r
      have hh := hgap j (fwWideSignedGapSlot n side r)
      have hcell := fun s : Bool => fw_wide_reindexed_diagonal_cell hwide hs choice rows cols hr hc j
        (fwWideSignedGapRectangle side r) 0 s
      simp only [fw_wide_signed_gap_controller_index] at hcell
      change (entry a (fwWidePhysicalPairCells hwide hs choice rows cols hr hc
        ((j, Fin.cast (by omega : 3*(n+8)*2 = 6*(n+8))
          (finProdFinEquiv (fwWideSignedGapSlot n side r, (0 : Fin 2)))), true)) : ℝ) =
        (entry a (fwWidePhysicalPairCells hwide hs choice rows cols hr hc
        ((j, Fin.cast (by omega : 3*(n+8)*2 = 6*(n+8))
          (finProdFinEquiv (fwWideSignedGapSlot n side r, (0 : Fin 2)))), false)) : ℝ) +
        gap j (π j (fwWideSignedGapSlot n side r)) at hh
      rw [hcell true, hcell false] at hh
      simpa [prefixPairCorner] using hh
    rw [fwWideSignedGapSlots, Finset.sum_image]
    swap
    · exact (fw_wide_signed_gap_slot_injective n side).injOn
    calc
      _ = ∑ r : Fin 12, (-(1/2 : ℝ) * gap j (π j (fwWideSignedGapSlot n side r))) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hp r]
        ring
      _ = _ := by rw [Finset.mul_sum]
end
end Sude
