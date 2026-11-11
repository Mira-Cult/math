import Sude.PhysicalProbabilitySlots
import Sude.InjectiveSlotWeights

/-! Transfer actual physical pair invoices to allocator slot coordinates. -/
namespace Sude
noncomputable section

/-- Actual physical labels occupy these distinct allocator pair slots. -/
def physicalPrefixSlots {d layers n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q) : Finset (Fin Q) :=
  Finset.univ.image (prefixStagePairSlot hfit hdiag)

/-- The actual row incidence weights, extended by zero outside occupied slots. -/
noncomputable def physicalRowSlotWeight {P d layers n L Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (j : Fin P) (r : Fin n) : Fin Q → ℝ :=
  liftedSlotWeight (prefixStagePairSlot hfit hdiag)
    (prefixStageRowIncidence hrect hs choice rows cols hrows hcols j r)

/-- The actual column incidence weights, extended by zero outside occupied slots. -/
noncomputable def physicalColumnSlotWeight {P d layers n L Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (j : Fin P) (c : Fin n) : Fin Q → ℝ :=
  liftedSlotWeight (prefixStagePairSlot hfit hdiag)
    (prefixStageColumnIncidence hrect hs choice rows cols hrows hcols j c)

/-- Slot-indexed row invoice is exactly the physical rectangle plus
ordinary-network invoice; distinctness prevents double counting. -/
theorem physicalRowSlotWeight_sq_sum {P d layers n L Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (j : Fin P) (r : Fin n) :
    (∑ q ∈ physicalPrefixSlots hfit hdiag,
      (physicalRowSlotWeight hfit hdiag hrect hs choice rows cols hrows hcols j r q) ^ 2) =
      prefixRectangleStageInvoice hrect hs choice (fun c => c.1 = r) j +
        physicalRowStageInvoice rows cols hrows hcols j r := by
  rw [show (∑ q ∈ physicalPrefixSlots hfit hdiag,
      (physicalRowSlotWeight hfit hdiag hrect hs choice rows cols hrows hcols j r q) ^ 2) =
      ∑ x, (prefixStageRowIncidence hrect hs choice rows cols hrows hcols j r x) ^ 2 from
    liftedSlotWeight_sq_sum _ (prefixStagePairSlot_injective hfit hdiag) _]
  exact prefixStageRowIncidence_sq_sum hrect hs choice rows cols hrows hcols j r

/-- The analogous exact column invoice in allocator slot coordinates. -/
theorem physicalColumnSlotWeight_sq_sum {P d layers n L Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (j : Fin P) (c : Fin n) :
    (∑ q ∈ physicalPrefixSlots hfit hdiag,
      (physicalColumnSlotWeight hfit hdiag hrect hs choice rows cols hrows hcols j c q) ^ 2) =
      prefixRectangleStageInvoice hrect hs choice (fun x => x.2 = c) j +
        physicalColumnStageInvoice rows cols hrows hcols j c := by
  rw [show (∑ q ∈ physicalPrefixSlots hfit hdiag,
      (physicalColumnSlotWeight hfit hdiag hrect hs choice rows cols hrows hcols j c q) ^ 2) =
      ∑ x, (prefixStageColumnIncidence hrect hs choice rows cols hrows hcols j c x) ^ 2 from
    liftedSlotWeight_sq_sum _ (prefixStagePairSlot_injective hfit hdiag) _]
  exact prefixStageColumnIncidence_sq_sum hrect hs choice rows cols hrows hcols j c

/-- The probability theorem's row slot invoice is bounded by the actual
physical width invoice; no abstract physical supply is assumed. -/
theorem physicalRowSlot_weighted_invoice {P d layers n L Q : ℕ} (hd : d = 2 * layers)
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (reserved : Finset (Cell n))
    (packed : LayerPacking.PackedLayers reserved rows) (r : Fin n) (width : Fin P → ℝ) (z : ℝ)
    (hwidth : ∀ j, (width j) ^ 2 ≤ z ^ 2) :
    (∑ j, (width j) ^ 2 * ∑ q ∈ physicalPrefixSlots hfit hdiag,
      (physicalRowSlotWeight hfit hdiag hrect hs choice rows cols hrows hcols j r q) ^ 2) ≤
      3 * (d : ℝ) * (∑ j, (width j) ^ 2) + 4 * z ^ 2 := by
  simp_rw [physicalRowSlotWeight_sq_sum]
  simpa [add_comm] using physical_prefix_row_width_invoice hd hrect hs choice rows cols hrows hcols
    reserved packed r width z hwidth

/-- The corresponding physical column slot invoice. -/
theorem physicalColumnSlot_weighted_invoice {P d layers n L Q : ℕ} (hd : d = 2 * layers)
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (reserved : Finset (Cell n))
    (packed : LayerPacking.PackedLayers reserved cols) (c : Fin n) (width : Fin P → ℝ) (z : ℝ)
    (hwidth : ∀ j, (width j) ^ 2 ≤ z ^ 2) :
    (∑ j, (width j) ^ 2 * ∑ q ∈ physicalPrefixSlots hfit hdiag,
      (physicalColumnSlotWeight hfit hdiag hrect hs choice rows cols hrows hcols j c q) ^ 2) ≤
      3 * (d : ℝ) * (∑ j, (width j) ^ 2) + 4 * z ^ 2 := by
  simp_rw [physicalColumnSlotWeight_sq_sum]
  simpa [add_comm] using physical_prefix_column_width_invoice hd hrect hs choice rows cols hrows hcols
    reserved packed c width z hwidth

end
end Sude
