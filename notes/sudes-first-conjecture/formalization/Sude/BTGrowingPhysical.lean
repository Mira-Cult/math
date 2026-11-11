import Sude.BTGrowingPoolValues
import Sude.VariablePrefixPhysical

/-! Install the selected pairs of a growing-radius trace. -/
namespace Sude
noncomputable section

/-- Install traced variable-gap pairs into both diagonal rectangles and two
ordinary physical networks, preserving the earlier reservation. All supplied
values come from the exact prescribed pool and no endpoint is reused. -/
theorem BTGrowingTrace.install_diagonal_and_ordinary {g Q n : ℕ} {traceInitial traceFinal : Finset ℕ}
    {R last : ℕ} {stages : List BTSelectedStage} (trace : BTGrowingTrace g Q traceInitial R traceFinal last stages)
    {P d r L B : ℕ} (hlen : stages.length = P)
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (hpool : ∀ p ∈ traceInitial, p ∈ pool n) (prior : Finset ℕ)
    (havoid : ∀ p ∈ traceInitial, p ∉ prior)
    (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrlen : rowPerms.length = P * r) (hclen : colPerms.length = P * r)
    (hrderange : ∀ π ∈ rowPerms, ∀ i, π i ≠ i)
    (hcderange : ∀ π ∈ colPerms, ∀ i, π i ≠ i)
    (base : Finset (Cell n)) (hrload : ∀ i, (LayerPacking.rowUsed base i).card ≤ B)
    (hcload : ∀ i, (LayerPacking.colUsed base i).card ≤ B)
    (hcapacity : 4 * ((B + 2) + 2 * rowPerms.length + 2 * colPerms.length) + 8 < n)
    (a : Cell n ≃ Fin (n * n)) (hbase : ∀ c ∈ base, entry a c ∈ prior)
    (hfree : ∀ x : Fin (P * (4 * d)) × Fin 4,
      packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2) ∉ base) :
    ∃ (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = rowPerms.length)
      (hcols : cols.length = colPerms.length) (b : Cell n ≃ Fin (n * n)),
      rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
      LayerPacking.PackedLayers (base ∪ allocatedBridgeRectangleSupport hrect hs choice) rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        ((base ∪ allocatedBridgeRectangleSupport hrect hs choice) ∪ LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows) (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      (∀ x : Fin (P * (4 * d)) × Fin 4,
        entry b (packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) =
          (trace.poolValues hlen hpool (prefixRectangleInput hdiag x)).val) ∧
      (∀ x, entry b (LayerPacking.sequenceCell rows x) =
        (trace.poolValues hlen hpool (prefixNetworkInput hfit hrlen 0 (Fin.cast hrows x.1, x.2))).val) ∧
      (∀ x, entry b (LayerPacking.sequenceCell cols x).swap =
        (trace.poolValues hlen hpool (prefixNetworkInput hfit hclen 1 (Fin.cast hcols x.1, x.2))).val) ∧
      (∀ i e, entry b ((rows.get i).1 e, (rows.get i).2 e) =
        entry b (e, (rows.get i).2 e) +
          variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages hlen j).gap) hrlen (Fin.cast hrows i) e) ∧
      (∀ i e, entry b ((cols.get i).2 e, (cols.get i).1 e) =
        entry b ((cols.get i).2 e, e) +
          variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages hlen j).gap) hclen (Fin.cast hcols i) e) ∧
      (∀ c ∈ base, entry b c = entry a c) := by
  have hav : ∀ x, (trace.poolValues hlen hpool x).val ∉ prior := by
    intro ⟨⟨j, i⟩, side⟩
    exact havoid _ (trace.endpoint_mem_initial hlen j i side)
  exact install_variable_prefix_diagonal_and_ordinary hfit hdiag hrect hs choice
    (fun j => (BTStageTrace.stageAt stages hlen j).gap) (trace.poolValues hlen hpool)
    (trace.poolValues_injective hlen hpool) (trace.poolValues_gap hlen hpool) prior hav
    rowPerms colPerms hrlen hclen hrderange hcderange base hrload hcload hcapacity a hbase hfree


end
end Sude
