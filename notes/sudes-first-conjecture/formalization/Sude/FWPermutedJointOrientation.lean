import Sude.FWPermutedJointEdgeGaps
import Sude.FWReallocatedOrientation
import Sude.FWJointWideGrowthGaps

/-! Orientation of all four joint-layer families on the same reallocated
square. Seed and growth role equations and both permuted family equations
are supplied; no packing, graph, or flow is constructed. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

/-- Stage-permuted bridge and wide equations orient every ordinary layer of
both networks on the supplied square. -/
theorem fw_permuted_bridge_wide_layers_oriented {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc : List (LayerPacking.Layer n)) (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    (reserved : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n reserved batches j)
    (new : Cell n ≃ Fin (n*n))
    (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8))))
    (hbgap : ∀ j b p, entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,b,p),true)) =
      entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,b,p),false)) +
        ((fwBridgeStageBlock n reserved batches hvalid j (πb j b)).high₁ -
          (fwBridgeStageBlock n reserved batches hvalid j (πb j b)).low₁))
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (hwgap : ∀ j b p, entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),true)) =
      entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),false)) +
        fwPermutedWideSourceGap blocks hlen πw j b) :
    fwRowsOriented new br ∧ fwColumnsOriented new bc ∧
      fwRowsOriented new wr ∧ fwColumnsOriented new wc := by
  constructor
  · intro i e
    let jk : Fin 5 × Fin 3 := finProdFinEquiv.symm (Fin.cast hr i)
    have hi : Fin.cast hr.symm (finProdFinEquiv jk) = i := by
      dsimp only [jk]; rw [Equiv.apply_symm_apply, Fin.cast_cast]; rfl
    have h := fw_permuted_bridge_ordinary_edge_gap hrect hs choice br bc hr hc reserved batches hvalid
      new πb hbgap jk.1 (jk.2,e) false
    simp only [fwBridgeLayerCells, Bool.false_eq_true, ↓reduceIte, fwBridgeLayerIndex] at h
    rw [hi] at h
    change entry new ((br.get i).1 e, (br.get i).2 e) = entry new (e, (br.get i).2 e) + _ at h
    omega
  constructor
  · intro i e
    let jk : Fin 5 × Fin 3 := finProdFinEquiv.symm (Fin.cast hc i)
    have hi : Fin.cast hc.symm (finProdFinEquiv jk) = i := by
      dsimp only [jk]; rw [Equiv.apply_symm_apply, Fin.cast_cast]; rfl
    have h := fw_permuted_bridge_ordinary_edge_gap hrect hs choice br bc hr hc reserved batches hvalid
      new πb hbgap jk.1 (jk.2,e) true
    simp only [fwBridgeLayerCells, ↓reduceIte, fwBridgeLayerIndex] at h
    rw [hi] at h
    change entry new ((bc.get i).2 e, (bc.get i).1 e) = entry new ((bc.get i).2 e, e) + _ at h
    omega
  constructor
  · intro i e
    let jk : Fin (3 * (n / 450)) × Fin 3 := finProdFinEquiv.symm (Fin.cast hwr i)
    have hi : Fin.cast hwr.symm (finProdFinEquiv jk) = i := by
      dsimp only [jk]; rw [Equiv.apply_symm_apply, Fin.cast_cast]; rfl
    have h := fw_permuted_wide_ordinary_edge_gap hwide hs choice wr wc hwr hwc blocks hlen new πw
      (by simpa only [fwPermutedWideSourceGap] using hwgap) jk.1 (jk.2,e) false
    simp only [fwWidePhysicalCells, fwWideEdgeRole, Sum.elim_inr, fwWideOrdinaryCells,
      Bool.false_eq_true, ↓reduceIte, fwWideLayerIndex, LayerPacking.sequenceCell,
      LayerPacking.layerCell, hi] at h
    omega
  · intro i e
    let jk : Fin (3 * (n / 450)) × Fin 3 := finProdFinEquiv.symm (Fin.cast hwc i)
    have hi : Fin.cast hwc.symm (finProdFinEquiv jk) = i := by
      dsimp only [jk]; rw [Equiv.apply_symm_apply, Fin.cast_cast]; rfl
    have h := fw_permuted_wide_ordinary_edge_gap hwide hs choice wr wc hwr hwc blocks hlen new πw
      (by simpa only [fwPermutedWideSourceGap] using hwgap) jk.1 (jk.2,e) true
    simp only [fwWidePhysicalCells, fwWideEdgeRole, Sum.elim_inr, fwWideOrdinaryCells,
      ↓reduceIte, fwWideLayerIndex, LayerPacking.sequenceCell, LayerPacking.layerCell,
      hi, Bool.false_eq_true, Prod.swap_prod_mk] at h
    omega

/-- The same-square family equations imply oriented physical gap equations
for every layer of the joint row and column lists. -/
theorem fw_permuted_four_family_physical_gap_equations {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc : List (LayerPacking.Layer n)) (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    {stages : List BTSelectedStage} (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (reserved : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n reserved batches j)
    (new : Cell n ≃ Fin (n*n))
    (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8))))
    (hbgap : ∀ j b p, entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,b,p),true)) =
      entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,b,p),false)) +
        ((fwBridgeStageBlock n reserved batches hvalid j (πb j b)).high₁ -
          (fwBridgeStageBlock n reserved batches hvalid j (πb j b)).low₁))
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (hwgap : ∀ j b p, entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),true)) =
      entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),false)) +
        fwPermutedWideSourceGap blocks hlen πw j b)
    (hseedgap : ∀ j i, entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true)) =
      entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) + 2)
    (hrow : ∀ (i : Fin (stages.length * 3)) (e : Fin n),
      entry new (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, true))))) =
      entry new (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e)
    (hcol : ∀ (i : Fin (stages.length * 3)) (e : Fin n),
      entry new (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, true))))) =
      entry new (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e) :
    let rows := ((br ++ sr) ++ wr) ++ gr
    let cols := ((bc ++ sc) ++ wc) ++ gc
    (∀ i e, entry new ((rows.get i).1 e, (rows.get i).2 e) =
      entry new (e, (rows.get i).2 e) + fwPhysicalRowLayerGap new rows i e) ∧
    (∀ i e, entry new ((cols.get i).2 e, (cols.get i).1 e) =
      entry new ((cols.get i).2 e, e) + fwPhysicalColumnLayerGap new cols i e) := by
  obtain ⟨hbr, hbc, hwr, hwc⟩ := fw_permuted_bridge_wide_layers_oriented hrect hwide hs choice
    br bc hr hc wr wc hwr hwc reserved batches hvalid new πb hbgap blocks hlen πw hwgap
  obtain ⟨hsr, hsc⟩ := fw_reallocated_seed_family_orientations hseed hs choice sr sc hsr hsc new hseedgap
  obtain ⟨hgr, hgc⟩ := fw_growth_layers_ordered offset hoff hs choice gr gc hgr hgc new hrow hcol
  exact fw_four_family_physical_gap_equations new br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc

end
end Sude
