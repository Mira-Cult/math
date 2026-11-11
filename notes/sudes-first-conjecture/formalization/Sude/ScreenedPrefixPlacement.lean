import Sude.ScreenedPrefix

/-! Install actual screened-prefix pairs and retain physical midpoint bounds. -/
namespace Sude
noncomputable section

/-- A narrowed trace selected from the screened pool can be placed in the
actual diagonal rectangles and both ordinary networks while preserving the
previously reserved cells. Geometric and capacity conditions remain explicit. -/
theorem BTGrowingTrace.install_screened_narrow {n Q d r L B : ℕ} {reserved final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage} {width : ℝ}
    (trace : BTGrowingTrace 2 Q ((poolFinset n).filter (fun p => 43 < p) \ reserved)
      radius final last stages)
    (hn : 13 ≤ n * n) (hnarrow : NarrowedStages width stages)
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : stages.length * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrlen : rowPerms.length = stages.length * r) (hclen : colPerms.length = stages.length * r)
    (hrderange : ∀ π ∈ rowPerms, ∀ i, π i ≠ i)
    (hcderange : ∀ π ∈ colPerms, ∀ i, π i ≠ i)
    (base : Finset (Cell n)) (hrload : ∀ i, (LayerPacking.rowUsed base i).card ≤ B)
    (hcload : ∀ i, (LayerPacking.colUsed base i).card ≤ B)
    (hcapacity : 4 * ((B + 2) + 2 * rowPerms.length + 2 * colPerms.length) + 8 < n)
    (a : Cell n ≃ Fin (n * n)) (hbase : ∀ c ∈ base, entry a c ∈ reserved)
    (hfree : ∀ x : Fin (stages.length * (4 * d)) × Fin 4,
      packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2) ∉ base) :
    ∃ (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = rowPerms.length)
      (hcols : cols.length = colPerms.length) (b : Cell n ≃ Fin (n * n)),
      rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
      LayerPacking.PackedLayers (base ∪ allocatedBridgeRectangleSupport hrect hs choice) rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        ((base ∪ allocatedBridgeRectangleSupport hrect hs choice) ∪ LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows) (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      (∀ i e, entry b ((rows.get i).1 e, (rows.get i).2 e) =
        entry b (e, (rows.get i).2 e) +
          variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) hrlen (Fin.cast hrows i) e) ∧
      (∀ i e, entry b ((cols.get i).2 e, (cols.get i).1 e) =
        entry b ((cols.get i).2 e, e) +
          variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) hclen (Fin.cast hcols i) e) ∧
      (∀ j : Fin stages.length, ∀ u : Fin (4 * d), ∀ p : Fin 2,
        entry b (packedRectangleCorner hs choice
          (Fin.castLE hrect (finProdFinEquiv (j, u)), prefixPairCorner p true)) =
        entry b (packedRectangleCorner hs choice
          (Fin.castLE hrect (finProdFinEquiv (j, u)), prefixPairCorner p false)) +
            (BTStageTrace.stageAt stages rfl j).gap) ∧
      (∀ i : Fin rows.length, ∀ e f : Fin n,
        |((entry b (LayerPacking.sequenceCell rows (i, (e, false))) : ℝ) +
             entry b (LayerPacking.sequenceCell rows (i, (e, true)))) / 2 -
          ((entry b (LayerPacking.sequenceCell rows (i, (f, false))) : ℝ) +
             entry b (LayerPacking.sequenceCell rows (i, (f, true)))) / 2| < width) ∧
      (∀ i : Fin cols.length, ∀ e f : Fin n,
        |((entry b (LayerPacking.sequenceCell cols (i, (e, false))).swap : ℝ) +
             entry b (LayerPacking.sequenceCell cols (i, (e, true))).swap) / 2 -
          ((entry b (LayerPacking.sequenceCell cols (i, (f, false))).swap : ℝ) +
             entry b (LayerPacking.sequenceCell cols (i, (f, true))).swap) / 2| < width) ∧
      (∀ j : Fin stages.length, ∀ u v : Fin (4 * d), ∀ p q : Fin 2,
        |((entry b (packedRectangleCorner hs choice
              (Fin.castLE hrect (finProdFinEquiv (j, u)), prefixPairCorner p false)) : ℝ) +
             entry b (packedRectangleCorner hs choice
              (Fin.castLE hrect (finProdFinEquiv (j, u)), prefixPairCorner p true))) / 2 -
          ((entry b (packedRectangleCorner hs choice
              (Fin.castLE hrect (finProdFinEquiv (j, v)), prefixPairCorner q false)) : ℝ) +
             entry b (packedRectangleCorner hs choice
              (Fin.castLE hrect (finProdFinEquiv (j, v)), prefixPairCorner q true))) / 2| < width) ∧
      (∀ c ∈ base, entry b c = entry a c) := by
  let S := (poolFinset n).filter (fun p => 43 < p) \ reserved
  have hstock := screened_pool_after_reservations n reserved hn
  have hpool : ∀ p ∈ S, p ∈ pool n := fun p hp => (hstock.2 p hp).1
  have havoid : ∀ p ∈ S, p ∉ reserved := fun p hp => (Finset.mem_sdiff.mp hp).2
  obtain ⟨rows, cols, hrows, hcols, b, hrmap, hcmap, hrpack, hcpack, hdisjoint,
    hrectplaced, hrplaced, hcplaced, hrgap, hcgap, hfixed⟩ :=
    trace.install_diagonal_and_ordinary rfl hfit hdiag hrect hs choice hpool reserved havoid
      rowPerms colPerms hrlen hclen hrderange hcderange base hrload hcload hcapacity a hbase hfree
  have hmid := trace.packed_networks_midpoints hnarrow rfl hpool hfit rows cols rowPerms colPerms
    hrows hcols hrlen hclen b hrplaced hcplaced
  have hrectmid := trace.placed_rectangle_midpoints hnarrow rfl hpool hdiag b
    (fun x => packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) hrectplaced
  have hrectgap := trace.placed_rectangle_pair_gap rfl hpool hdiag b
    (fun x => packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) hrectplaced
  exact ⟨rows, cols, hrows, hcols, b, hrmap, hcmap, hrpack, hcpack, hdisjoint,
    hrgap, hcgap, hrectgap, hmid.1, hmid.2, hrectmid, hfixed⟩

end
end Sude
