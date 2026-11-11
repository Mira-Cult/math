import Sude.FWThetaSeedBridgeWideConcentration
import Sude.FWBalancedFreshWideAllLineReallocation
import Sude.FWSeedFreshMidpointsRadiusUpper

/-! A fresh theta witness retaining all seed/bridge/wide midpoint outputs and
same-square centered wide gap facts and a radius bound on the same trace.
Spare values and raw midpoint contrast
remain separate; no equality to another selected witness is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000

theorem bmor_fw_seed_bridge_wide_fresh_gap_radius_upper_of_theta
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    (n : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    let hrect := (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).1
    let hseedrect := (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).2.1
    let hwide := (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).2.2.1
    let hs := (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).2.2.2
    let hmax := fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)
    let choice := fwBridgeSeedRectangleChoice hrect hseedrect
      (fwWideRectangleChoice hwide (fwGrowthRectangleChoice hmax otherChoice))
    ∃ p : Fin 3 → Equiv.Perm (Fin n),
      (∀ i v, p i v ≠ v) ∧
      (∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
        500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card) ∧
    ∃ (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j),
    ∃ (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
      (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16),
      candidates ⊆ seeds ∧
    ∃ (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
      (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
      (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
      (hwc : wc.length = (3 * (n / 450)) * 3)
      (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
      (old : Cell n ≃ Fin (n*n)) (stock : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
    let initial := ((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
    let offset := 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)
    ∃ (trace : BTGrowingTrace 2 (6 * (n + 8)) initial 32 stock last stages)
      (hoff : offset + stages.length * (4 * 6) ≤ fwJointRectangleCount n 254)
      (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3)
      (hgc : gc.length = stages.length * 3) (grown : Cell n ≃ Fin (n*n)),
      stages.length ≤ 238 ∧
      stock ⊆ initial ∧
      stock.card + 2 * (6 * (n + 8)) * stages.length = initial.card ∧
      (poolMaximum n : ℝ) / 23 ≤ last ∧
      (last : ℝ) ≤ max (32 : ℝ) (2 * ((poolMaximum n : ℝ) / 23)) ∧
      stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ stage ∈ stages, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) stages ∧
      (∀ c ∈ fwGrowthEarlyRoleCells hrect hseedrect hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc,
        entry grown c = entry old c) ∧
      rows.map Prod.fst = bridgeRepeatedPermutations 5 p ∧
      cols.map Prod.fst = bridgeRepeatedPermutations 5 p ∧
      sr.map Prod.fst = bridgeRepeatedPermutations 16 p ∧
      sc.map Prod.fst = bridgeRepeatedPermutations 16 p ∧
      gr.map Prod.fst = bridgeRepeatedPermutations stages.length p ∧
      gc.map Prod.fst = bridgeRepeatedPermutations stages.length p ∧
      LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((rows ++ sr) ++ wr) ++ gr) ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((rows ++ sr) ++ wr) ++ gr)))
          (((cols ++ sc) ++ wc) ++ gc) ∧
      (∀ x : PrefixPhysicalInputs stages.length 6 3 n,
        entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
          (trace.poolValues rfl (by intro v hv; exact mem_poolFinset.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1)
            (prefixPhysicalInput (by omega) (by omega) x)).val) ∧
      (let m : ℝ := (Lucas.poolTotal n : ℝ) / (n * n : ℕ)
       let low := bmorLowBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
       let high := bmorHighBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
       ∀ block ∈ blocks, block.MatchedValid low high) ∧
      (∀ (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) (side : Bool),
        fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e false side) =
          ((if side then p k e else e), (wr.get (bridgeStageLayerIndex hwr j k)).2 e) ∧
        fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e true side) =
          ((wc.get (bridgeStageLayerIndex hwc j k)).2 e, (if side then p k e else e))) ∧
      (let cells := fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc
       let line := fun l : Fin ((n+n)+2) => fun c => c ∈ physicalAllLineCells l
       let weights := fun l j q => physicalPairLineWeight cells (line l) (j, q)
       let values := fun j q => (((entry grown (cells ((j, q), false)) : ℝ) +
         entry grown (cells ((j, q), true))) / 2)
       let V : ℝ := (11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2
       let B := Real.sqrt (V * Real.log (4 * (((n + n) + 2 : ℕ) : ℝ)) / 2)
       ∃ (ω : Fin 16 → Equiv.Perm (Fin (6 * (n + 8)))) (b : Cell n ≃ Fin (n*n)),
         (∀ j i side, entry b (cells ((j, i), side)) = entry grown (cells ((j, ω j i), side))) ∧
         (∀ x : PrefixPhysicalInputs stages.length 6 3 n,
           entry b (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
             entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x)) ∧
         Finset.univ.image (fun x => entry b (cells x)) =
           retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub ∧
         (∀ j i, entry b (cells ((j, i), true)) = entry b (cells ((j, i), false)) + 2) ∧
         (∀ l, |stageLineCentered (fun _ _ => Finset.univ) weights values l ω| ≤ B) ∧
         (∀ l, |(∑ c ∈ (Finset.univ.image cells).filter (line l), (entry b c : ℝ)) -
           (∑ j, ((∑ q, weights l j q) * ((∑ q, values j q) / ((6 * (n + 8) : ℕ) : ℝ)))) -
           (∑ p, physicalPairLineOrientation cells (line l) p * ((2 : ℝ) / 2))| ≤ B) ∧
         (∀ t side, entry b (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
           fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeDiagonalSlot n (t, side))) ∧
         (∀ x, entry b (fwBridgeLayerCells rows cols hr hc x) =
           fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x)) ∧
         (∀ x : FWWideInputs n, entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
           doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2)) ∧
       let bridge := fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc
       let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
       let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
         offset hoff hs choice gr gc hgr hgc
       let gapb := fun j k => (fwBridgeStageBlock n ∅ batches hvalid j k).high₁ -
         (fwBridgeStageBlock n ∅ batches hvalid j k).low₁
       let gapw := fun j k =>
         let block := blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,k)))
         block.high₁ - block.low₁
       ∃ (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8)))) (sb : (Fin 5 × Fin (3 * (n + 8))) → Bool)
         (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
         (sw : (Fin (3 * (n / 450)) × Fin (3 * (n + 8))) → Bool)
         (new : Cell n ≃ Fin (n * n)),
         (∀ j k p side, entry new (bridge ((j,k,p),side)) =
           entry b (bridge ((j,πb j k,doubleBlockPairSwap (sb (j,k)) p),side))) ∧
         (∀ j k p side, entry new (wide ((j,k,p),side)) =
           entry b (wide ((j,πw j k,doubleBlockPairSwap (sw (j,k)) p),side))) ∧
         (∀ x, entry new (cells x) = entry b (cells x)) ∧
         (∀ x, entry new (growth x) = entry b (growth x)) ∧
         (∀ x : PrefixPhysicalInputs stages.length 6 3 n,
           entry new (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
             entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x)) ∧
         Finset.univ.image (fun x => entry new (cells x)) =
           retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub ∧
         (∀ c, c ∉ Set.range bridge → c ∉ Set.range wide → entry new c = entry b c) ∧
         (∀ j, Finset.univ.image (fun x : (Fin (3 * (n + 8)) × Fin 2) × Bool =>
           entry new (bridge ((j,x.1.1,x.1.2),x.2))) =
           Finset.univ.image (fun x : (Fin (3 * (n + 8)) × Fin 2) × Bool =>
           entry b (bridge ((j,x.1.1,x.1.2),x.2)))) ∧
         (∀ j, Finset.univ.image (fun x : (Fin (3 * (n + 8)) × Fin 2) × Bool =>
           entry new (wide ((j,x.1.1,x.1.2),x.2))) =
           Finset.univ.image (fun x : (Fin (3 * (n + 8)) × Fin 2) × Bool =>
           entry b (wide ((j,x.1.1,x.1.2),x.2)))) ∧
         (∀ j k p, entry new (bridge ((j,k,p),true)) =
           entry new (bridge ((j,k,p),false)) + gapb j (πb j k)) ∧
         (∀ j k p, entry new (wide ((j,k,p),true)) =
           entry new (wide ((j,k,p),false)) + gapw j (πw j k)) ∧
         (∀ j k, 0 < gapw j (πw j k)) ∧
         (∀ l, |doubleBlockActualCenteredScore bridge (line l) b new| <
           (poolMaximum n : ℝ) * (23 / 924 : ℝ) * Real.sqrt (94 * Real.log (8 * (n : ℝ) + 8))) ∧
         (∀ l, |doubleBlockActualCenteredScore wide (line l) b new| <
           (poolMaximum n : ℝ) * (2 / 235 : ℝ) *
             Real.sqrt ((54 * ((n / 450 : ℕ) : ℝ) + 4) * Real.log (8 * (n : ℝ) + 8))) ∧
      (∀ j side r, (if side = true then packedRectangleCorner hs choice
        (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0) ∈ mainCells n
        else packedRectangleCorner hs choice
        (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0) ∈ antiCells n)) ∧
      (∀ j side, (∑ r : Fin 12,
        ((entry new (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0)) : ℝ) -
         ((entry new (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0)) : ℝ) +
          (entry new (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),1)) : ℝ))/2)) =
        -(1/2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n side, (gapw j (πw j b) : ℝ)) ∧
      |(1/2 : ℝ) * ((∑ j, ∑ b ∈ fwWideSignedGapSlots n true, (gapw j (πw j b) : ℝ)) -
        ∑ j, ∑ b ∈ fwWideSignedGapSlots n false, (gapw j (πw j b) : ℝ))| <
        2 * Real.sqrt ((3/2 : ℝ) * ((3*(n/450) : ℕ) : ℝ) * ((64/235 : ℝ)*(poolMaximum n : ℝ))^2 * Real.log 16) ∧
         (∀ j i side, entry new (cells ((j, i), side)) = entry grown (cells ((j, ω j i), side))) ∧
         (∀ j i, entry new (cells ((j, i), true)) = entry new (cells ((j, i), false)) + 2) ∧
         (∀ l, |(∑ c ∈ (Finset.univ.image cells).filter (line l), (entry new c : ℝ)) -
           (∑ j, ((∑ q, weights l j q) * ((∑ q, values j q) / ((6 * (n + 8) : ℕ) : ℝ)))) -
           (∑ p, physicalPairLineOrientation cells (line l) p * ((2 : ℝ) / 2))| ≤ B)) := by
  classical
  intro hrect hseedrect hwide hs hmax choice
  have hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  have hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  have hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  have hn16 : 450 ≤ n := by omega
  have hn35733 : n ≤ 35733 := by omega
  have hXnat : 100 ≤ poolMaximum n := by
    have hp := fw_poolMaximum_gt_four_seed lower hnlo
    omega
  have hmain := bmor_fw_seed_concentration_fresh_midpoints_of_theta_radius_upper
    mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hprime hcount
  dsimp only at hmain ⊢
  refine hmain.imp fun p hp => ⟨hp.1, hp.2.1, ?_⟩
  refine hp.2.2.imp fun batches hbatches => hbatches.imp fun hvalid hcand0 => ?_
  refine hcand0.imp fun candidates hcand1 => hcand1.imp fun hcard hcand2 => ?_
  refine hcand2.imp fun kept hcand3 => hcand3.imp fun hsub hcand4 => ?_
  refine hcand4.imp fun hkept hcand5 => ⟨hcand5.1, ?_⟩
  refine hcand5.2.2.2.2.imp fun rows hrows0 => hrows0.imp fun cols hcols0 => ?_
  refine hcols0.imp fun hr hhr0 => hhr0.imp fun hc hhc0 => ?_
  refine hhc0.imp fun sr hsr0 => hsr0.imp fun sc hsc0 => ?_
  refine hsc0.imp fun hsr hhsr0 => hhsr0.imp fun hsc hhsc0 => ?_
  refine hhsc0.imp fun wr hwr0 => hwr0.imp fun wc hwc0 => ?_
  refine hwc0.imp fun hwr hhwr0 => hhwr0.imp fun hwc hhwc0 => ?_
  refine hhwc0.imp fun blocks hblocks0 => hblocks0.imp fun hlen hhlen0 => ?_
  refine hhlen0.imp fun old hold0 => hold0.imp fun stock hstock0 => ?_
  refine hstock0.imp fun last hlast0 => hlast0.imp fun stages hstages0 => ?_
  refine hstages0.imp fun trace htrace0 => htrace0.imp fun hoff hhoff0 => ?_
  refine hhoff0.imp fun gr hgr0 => hgr0.imp fun gc hgc0 => ?_
  refine hgc0.imp fun hgr hhgr0 => hhgr0.imp fun hgc hhgc0 => ?_
  refine hhgc0.imp fun grown hgrown => ?_
  have hcap := hgrown.1
  have hfixed := hgrown.2.2.2.2.2.2.2.2.2.2.1
  have hg1 := hgrown.2.2.2.2.2.2.2.2.2.2.2
  have hg2 := hg1.2.2.2.2.2.2.2.2.2.2
  have hjointrow := hg2.2.2.2.2.1
  have hjointcol := hg2.2.2.2.2.2.1
  have hg3 := hg2.2.2.2.2.2.2.2.2.2.2
  have hbd := hg3.2.2.1
  have hbo := hg3.2.2.2.2.2.1
  have hmatched := hg3.2.2.2.2.2.2.2.2.1
  have hg4 := hg3.2.2.2.2.2.2.2.2.2.2
  have hwp := hg4.2.1
  refine ⟨hcap, hgrown.2.1, hgrown.2.2.1, hgrown.2.2.2.2.2.1, hgrown.2.2.2.2.2.2.1,
    hgrown.2.2.2.2.2.2.2.1, hgrown.2.2.2.2.2.2.2.2.1, hgrown.2.2.2.2.2.2.2.2.2.1, hfixed,
    hg1.1, hg1.2.1, hg1.2.2.1, hg1.2.2.2.1, hg1.2.2.2.2.1, hg1.2.2.2.2.2.1,
    hjointrow, hjointcol, hg2.2.2.2.2.2.2.2.2.2.1, hmatched, hg4.2.2.2.1, ?_⟩
  refine hg4.2.2.2.2.2.2.2.2.2.2.imp fun ω hω => hω.imp fun b hb => ?_
  have hperm := hb.1
  have hset := hb.2.2.2.1
  have hgap := hb.2.2.2.2.1
  have hcenter := hb.2.2.2.2.2.1
  have hselected := hb.2.2.2.2.2.2.1
  obtain ⟨_, _, hbdPres, hbridgePres, hwidePres, hgrowthPres, _⟩ := hb.2.2.2.2.2.2.2
  have hchoice : fwBridgeSeedWideGrowthChoice hrect hseedrect hwide hoff choice = choice :=
    fw_theta_witness_choice_retract_realized hrect hseedrect hwide hmax hoff hcap otherChoice
  obtain ⟨hbdB, hboB, hwpB⟩ := fw_bridge_wide_placement_transfer hrect hseedrect hwide hs choice
    rows cols sr sc wr wc hr hc hsr hsc hwr hwc ∅ batches hvalid blocks hlen old grown b
    hfixed hbdPres hbridgePres hwidePres hbd hbo hwp
  have hX : (100 : ℝ) ≤ poolMaximum n := by exact_mod_cast hXnat
  obtain ⟨hmlo, hmhi⟩ := fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo hn35733
  obtain ⟨πb, sb, πw, sw, new, hbe, hwe, hseedNew, hgrowthNew, hnewOutside,
    hbstage, hwstage, hbgaps, hwgaps, hbgap, hwgap, hwpos, hbscore, hwscore, hside, hcenteredWide, hcontrast⟩ :=
    fw_balanced_all_line_fresh_wide_reallocation hn16 hcap hrect hseedrect hwide hoff hs choice
      rows cols sr sc wr wc gr gc hr hc hsr hsc hwr hwc hgr hgc
      (by simpa only [hchoice] using hjointrow) (by simpa only [hchoice] using hjointcol)
      b ∅ batches hvalid (by simpa only [hchoice] using hbdB) hboB blocks hlen
      ((Lucas.poolTotal n : ℝ) / (n*n : ℕ)) hX hmlo hmhi hmatched
      (by simpa only [hchoice] using hwpB)
  simp only [hchoice] at hbe hwe hseedNew hgrowthNew hnewOutside hbstage hwstage hbgaps hwgaps hbgap hwgap hwpos hbscore hwscore hside hcenteredWide hcontrast
  let cells := fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc
  let line := fun l : Fin ((n+n)+2) => fun c => c ∈ physicalAllLineCells l
  let V : ℝ := (11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2
  let B := Real.sqrt (V * Real.log (4 * (((n + n) + 2 : ℕ) : ℝ)) / 2)
  have hpermNew := seed_pair_permutation_preserved cells grown b new ω hseedNew hperm
  have hselectedNew := seed_source_midpoint_concentration_preserved cells line grown b new B hseedNew hselected
  have hgrowthRoleNew : ∀ x : PrefixPhysicalInputs stages.length 6 3 n,
      entry new (btGrowingOffsetCells (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
        hoff hs choice gr gc hgr hgc x) =
      entry grown (btGrowingOffsetCells (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
        hoff hs choice gr gc hgr hgc x) := by
    intro x
    have h := hgrowthNew ((prefixPhysicalInputEquiv (P := stages.length) (d := 6) (layers := 3)
      (n := n) (Q := 6 * (n + 8)) hfit hdiag hexact) x)
    have h' : entry new (btGrowingOffsetCells _ hoff hs choice gr gc hgr hgc x) =
        entry b (btGrowingOffsetCells _ hoff hs choice gr gc hgr hgc x) := by
      simpa only [btGrowingOffsetPairCells, Equiv.symm_apply_apply] using h
    exact h'.trans (hgrowthPres x)
  have hsetNew : Finset.univ.image (fun x => entry new (cells x)) =
      retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub := by
    have heq : (fun x => entry new (cells x)) = (fun x => entry b (cells x)) :=
      funext (fun x => hseedNew x)
    rw [heq]
    exact hset
  have hgapNew : ∀ j i, entry new (cells ((j,i),true)) = entry new (cells ((j,i),false)) + 2 := by
    intro j i
    calc
      entry new (cells ((j,i),true)) = entry b (cells ((j,i),true)) := hseedNew _
      _ = entry b (cells ((j,i),false)) + 2 := hgap j i
      _ = entry new (cells ((j,i),false)) + 2 := congrArg (fun z => z + 2) (hseedNew _).symm
  exact ⟨hperm, hgrowthPres, hset, hgap, hcenter, hselected, hbdB, hboB, hwpB,
    πb, sb, πw, sw, new, hbe, hwe, hseedNew, hgrowthNew, hgrowthRoleNew, hsetNew, hnewOutside,
    hbstage, hwstage, hbgap, hwgap, hwpos, hbscore, hwscore, hside, hcenteredWide, hcontrast,
    hpermNew, hgapNew, hselectedNew⟩


end
end Sude
