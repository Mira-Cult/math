import Sude.FWActiveRoleInvoice
import Sude.ActiveSupportCenteredInvoice
import Sude.FWRoleSupportEquality
import Sude.FWPhysicalMidpointInvoice
import Sude.FWActualJointGapTotal

/-! Compare a fresh active-role reference to actual physical midpoints.
A supplied trace and physical gap identities establish the block totals.
No theta witness, target existence, or global mean estimate is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

/-- A supplied trace and physical pair identities for the same wide family
allow the fresh active-role reference to be compared to physical midpoints. -/
theorem fw_actual_explicit_wide_active_role_midpoint_invoice {n Q : ℕ} {initial final : Finset ℕ}
    (grown : Cell n ≃ Fin (n*n)) (rect : Finset (Cell n))
    (p : Fin 3 → Equiv.Perm (Fin n)) (batches : ℕ → List DoublePair) (last : ℕ)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (stages : List BTSelectedStage) (trace : BTGrowingTrace 2 Q initial 32 final last stages)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (hP : stages.length ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + stages.length * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (hrows : LayerPacking.PackedLayers rect (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
    (hrowGap : ∀ i e, entry grown (((((br ++ sr) ++ wr) ++ gr).get i).1 e,
        ((((br ++ sr) ++ wr) ++ gr).get i).2 e) =
      entry grown (e, ((((br ++ sr) ++ wr) ++ gr).get i).2 e) +
        fwPhysicalRowLayerGap grown (((br ++ sr) ++ wr) ++ gr) i e)
    (hcolGap : ∀ i e, entry grown (((((bc ++ sc) ++ wc) ++ gc).get i).2 e,
        ((((bc ++ sc) ++ wc) ++ gc).get i).1 e) =
      entry grown (((((bc ++ sc) ++ wc) ++ gc).get i).2 e, e) +
        fwPhysicalColumnLayerGap grown (((bc ++ sc) ++ wc) ++ gc) i e)
    (wide : (Fin 3 × Fin n) → Fin (3 * (n / 450)) → ℕ)
    (hgrids : ∀ edge : Fin 3 × Fin n,
      let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
      let radius := last + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j
      let labels := fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))
      let rows := ((br ++ sr) ++ wr) ++ gr
      let cols := ((bc ++ sc) ++ wc) ++ gc
      let rowSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)
      let colSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)
      CompleteEvenGrid (labels.attach.image rowSlot) (fun x => fwPhysicalRowLayerGap grown rows x.1 x.2)
          (radius + ∑ j, wide edge j) ∧
        CompleteEvenGrid (labels.attach.image colSlot) (fun x => fwPhysicalColumnLayerGap grown cols x.1 x.2)
          (radius + ∑ j, wide edge j) ∧
        (∀ x side, LayerPacking.sequenceCell rows ((rowSlot x).1, ((rowSlot x).2, side)) =
          ((if side then p edge.1 edge.2 else edge.2), (rows.get (rowSlot x).1).2 edge.2)) ∧
        (∀ x side, (LayerPacking.sequenceCell cols ((colSlot x).1, ((colSlot x).2, side))).swap =
          ((cols.get (colSlot x).1).2 edge.2, (if side then p edge.1 edge.2 else edge.2))) ∧
        (2 : ℝ) * (n / 450 : ℕ) * (poolMaximum n : ℝ) ≤ ∑ j, (wide edge j : ℝ))
    (hplace : ∀ x, entry grown (fwBridgeLayerCells br bc hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    (hwidepair : ∀ (edge : Fin 3 × Fin n) (j : Fin (3 * (n / 450))) (network : Bool),
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide edge j)
    (hseedpair : ∀ (edge : Fin 3 × Fin n) (network : Bool) (i : Fin 16),
      entry grown (fwSeedEdgeCells sr sc hsr hsc edge network i true) =
      entry grown (fwSeedEdgeCells sr sc hsr hsc edge network i false) + 2)
    (hgrowthpair : ∀ (edge : Fin 3 × Fin n) (network : Bool) (i : Fin stages.length),
      entry grown (fwGrowthEdgeCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
        hoff hs choice gr gc hgr hgc edge network i true) =
      entry grown (fwGrowthEdgeCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
        hoff hs choice gr gc hgr hgc edge network i false) +
      (BTStageTrace.stageAt stages rfl i).gap) :
    let N := (n / 450) * poolMaximum n
    let source : Fin 3 × Fin n → Fin n := fun e => e.2
    let target : Fin 3 × Fin n → Fin n := fun e => p e.1 e.2
    let rowLayers := ((br ++ sr) ++ wr) ++ gr
    let colLayers := ((bc ++ sc) ++ wc) ++ gc
    let rowGap := fwPhysicalRowLayerGap grown rowLayers
    let colGap := fwPhysicalColumnLayerGap grown colLayers
    let active := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hr hc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
    ∃ (BR : CenteredNetwork (Fin 3 × Fin n) (Fin rowLayers.length × Fin n)
        (hrows.rowPairs grown rowGap hrowGap))
      (BC : CenteredNetwork (Fin 3 × Fin n) (Fin colLayers.length × Fin n)
        (hcols.columnPairs grown colGap hcolGap))
      (b₀ : Cell n ≃ Fin (n*n)),
      TwoNetworkReferenceInvoice grown b₀ rowLayers colLayers hrows hcols rowGap colGap
        hrowGap hcolGap BR BC ∧
      (∀ edge, BR.source edge = edge.2 ∧ BC.source edge = edge.2 ∧
        BR.target edge = p edge.1 edge.2 ∧ BC.target edge = p edge.1 edge.2) ∧
      (∀ edge, BR.block edge =
        (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
          (fun x => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2))) ∧
      (∀ edge, BC.block edge =
        (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
          (fun x => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2))) ∧
      (∀ edge, BR.radius edge = last +
        (∑ j ∈ Finset.range 5, selectedBridgeGap batches
          (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge) j) + ∑ j, wide edge j) ∧
      (∀ edge, BC.radius edge = BR.radius edge) ∧
      (∀ edge, (∑ k ∈ BR.block edge, (hrows.rowPairs grown rowGap hrowGap).gap k) = BR.radius edge ∧
        (∑ k ∈ BC.block edge, (hcols.columnPairs grown colGap hcolGap).gap k) = BC.radius edge) ∧
      (∀ r, |2 * (rowSum b₀ r : ℤ) -
        physicalNetworkMidpointTwice (hrows.rowPairs grown rowGap hrowGap) BR r| ≤ 9) ∧
      (∀ c, |2 * (columnSum b₀ c : ℤ) -
        physicalNetworkMidpointTwice (hcols.columnPairs grown colGap hcolGap) BC c| ≤ 9) ∧
      (∀ edge, 2 * N ≤ BR.radius edge) ∧
      mainSum b₀ = mainSum grown ∧ antiSum b₀ = antiSum grown ∧
      (∀ c ∈ rect, entry b₀ c = entry grown c) ∧
      (∀ c ∉ active, entry b₀ c = entry grown c) ∧
      active.image (entry b₀) = active.image (entry grown) ∧
      Set.range (entry b₀) = pool n ∧ Function.Injective (entry b₀) ∧
      ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∃ b : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer source target fr e r) ∧
        (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer source target fc e c) ∧
        mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
        (∀ c ∈ rect, entry b c = entry b₀ c) ∧
        (∀ c ∉ active, entry b c = entry grown c) ∧
        active.image (entry b) = active.image (entry grown) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  dsimp only
  obtain ⟨BR, BC, b₀, hinvoice, hends, hblocksR, hblocksC, hradius, hsame,
    hcapacity, hm, ha, hfixed, houtside, himage, hpool, hinj, hflows⟩ :=
    fw_actual_explicit_wide_active_role_invoice grown rect p batches last
      br bc sr sc wr wc gr gc hr hc hsr hsc hwr hwc hgr hgc
      hP hrect hseed hwide hoff hs choice hrows hcols hrowGap hcolGap wide hgrids
  have hactualTotal (edge : Fin 3 × Fin n) :=
    fw_actual_joint_grid_gap_totals batches hvalid hrect hseed hwide hs choice
      br bc hr hc sr sc hsr hsc wr wc hwr hwc grown grown (by intro c hc; rfl) hplace
      trace (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
      hoff gr gc hgr hgc edge (wide edge) (hwidepair edge) (hseedpair edge) (hgrowthpair edge)
  have hrowTotal : ∀ edge, (∑ k ∈ BR.block edge,
      (hrows.rowPairs grown (fwPhysicalRowLayerGap grown (((br ++ sr) ++ wr) ++ gr)) hrowGap).gap k) = BR.radius edge := by
    intro edge
    rw [hblocksR edge, hradius edge]
    exact (hactualTotal edge).1
  have hcolTotal : ∀ edge, (∑ k ∈ BC.block edge,
      (hcols.columnPairs grown (fwPhysicalColumnLayerGap grown (((bc ++ sc) ++ wc) ++ gc)) hcolGap).gap k) = BC.radius edge := by
    intro edge
    rw [hblocksC edge, hsame edge, hradius edge]
    exact (hactualTotal edge).2
  have hmids := fw_reference_invoice_physical_midpoint_bounds p grown b₀ rect
    (((br ++ sr) ++ wr) ++ gr) (((bc ++ sc) ++ wc) ++ gc) hrows hcols
    (fwPhysicalRowLayerGap grown _) (fwPhysicalColumnLayerGap grown _) hrowGap hcolGap
    BR BC hends hrowTotal hcolTotal hinvoice
  exact ⟨BR, BC, b₀, hinvoice, hends, hblocksR, hblocksC, hradius, hsame,
    (fun edge => ⟨hrowTotal edge, hcolTotal edge⟩), hmids.1, hmids.2,
    hcapacity, hm, ha, hfixed, houtside, himage, hpool, hinj, hflows⟩

end
end Sude
