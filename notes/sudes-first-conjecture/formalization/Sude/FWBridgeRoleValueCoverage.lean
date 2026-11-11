import Sude.FWBridgeLayerSlots
import Sude.FWBridgeControllerSlots
import Sude.FWBridgeSeedCoverage

/-! Bridge role-cell values cover the actual five-stage batch reservation. -/
namespace Sude
noncomputable section

/-- For one square, if the supplied bridge rectangle and ordinary-layer
placements agree with their indexed batch endpoints, their value image is
exactly the final five-stage batch reservation. -/
theorem fw_bridge_role_values_eq_reservation {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (a : Cell n ≃ Fin (n * n))
    (hdiag : ∀ t side, entry a (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (hord : ∀ x, entry a (fwBridgeLayerCells rows cols hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x)) :
    ((Finset.univ.image (fun x : Fin (5 * (4 * 6)) × Fin 4 =>
      packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect x.1, x.2)) ∪
      Finset.univ.image (fwBridgeLayerCells rows cols hr hc)).image (entry a)) =
      priorBridgeReservation ∅ (Finset.range 5) batches := by
  classical
  have hend : (Finset.univ.image (fwBridgeStageEndpoint n ∅ batches hvalid)) =
      priorBridgeReservation ∅ (Finset.range 5) batches :=
    fwBridge_reservation_eq_endpoints n batches hvalid
  rw [← hend]
  ext v
  simp only [Finset.mem_image, Finset.mem_union, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, (⟨x, rfl⟩ | ⟨x, rfl⟩), hv⟩
    · exact ⟨fwBridgeDiagonalSlot n x, by simpa [hdiag x.1 x.2] using hv⟩
    · exact ⟨fwBridgeOrdinarySlot n x, by simpa [hord x] using hv⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := (fwBridgeControllerSlot_bijective n).2 y
    cases x with
    | inl x =>
      change fwBridgeDiagonalSlot n x = y at hx
      refine ⟨_, Or.inl ⟨x, rfl⟩, ?_⟩
      simpa [hdiag x.1 x.2, hx] using hy
    | inr x =>
      change fwBridgeOrdinarySlot n x = y at hx
      refine ⟨_, Or.inr ⟨x, rfl⟩, ?_⟩
      simpa [hord x, hx] using hy

end
end Sude
