import Sude.FWThetaFamilyWitness
import Sude.FWThetaNetworkWitness
import Sude.FWThetaGrowthDiagonalWitness
import Sude.FWThetaRoleValueInputs
import Sude.FWThetaAllFamilyFreshWideGapRadiusUpper

/-! Project the family, network, growth-diagonal and role-value inputs from
one actual theta witness. The result supplies no DQ/RF completion, numerical
or primality gate and asserts no later-flow bound. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 20000000

/-- Facts carried from one fresh theta selection to its exact intermediate,
ordered and reference squares. No later-flow or prime-target conclusion. -/
structure FWThetaFreshWideProjection {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice) (intermediate reference : Cell n ≃ Fin (n*n)) : Prop where
  radius_lower : (poolMaximum n : ℝ) / 23 ≤ f.last
  radius_upper : (f.last : ℝ) ≤ max (32 : ℝ) (2 * ((poolMaximum n : ℝ) / 23))
  side : ∀ j side r, (if side = true then packedRectangleCorner f.hs choice
    (fwWideRectangle f.hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)), 0) ∈ mainCells n
    else packedRectangleCorner f.hs choice
    (fwWideRectangle f.hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)), 0) ∈ antiCells n)
  intermediate_centered : ∀ j side, (∑ r : Fin 12,
    ((entry intermediate (packedRectangleCorner f.hs choice
      (fwWideRectangle f.hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)), 0)) : ℝ) -
     ((entry intermediate (packedRectangleCorner f.hs choice
      (fwWideRectangle f.hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)), 0)) : ℝ) +
      (entry intermediate (packedRectangleCorner f.hs choice
      (fwWideRectangle f.hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)), 1)) : ℝ))/2)) =
    -(1/2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n side, (f.gapw j b : ℝ)
  contrast : |(1/2 : ℝ) * ((∑ j, ∑ b ∈ fwWideSignedGapSlots n true, (f.gapw j b : ℝ)) -
    ∑ j, ∑ b ∈ fwWideSignedGapSlots n false, (f.gapw j b : ℝ))| <
    2 * Real.sqrt ((3/2 : ℝ) * ((3*(n/450) : ℕ) : ℝ) * ((64/235 : ℝ)*(poolMaximum n : ℝ))^2 * Real.log 16)
  ordered_centered : ∀ j side, (∑ r : Fin 12,
    ((entry f.ordered (packedRectangleCorner f.hs choice
      (fwWideRectangle f.hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)), 0)) : ℝ) -
     ((entry f.ordered (packedRectangleCorner f.hs choice
      (fwWideRectangle f.hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)), 0)) : ℝ) +
      (entry f.ordered (packedRectangleCorner f.hs choice
      (fwWideRectangle f.hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)), 1)) : ℝ))/2)) =
    -(1/2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n side,
      (let block := f.blocks.get (Fin.cast f.hlen.symm (finProdFinEquiv (j, f.πw j b))); (block.high₁ : ℝ) - (block.low₁ : ℝ))
  reference_centered : ∀ j side, (∑ r : Fin 12,
    ((entry reference (packedRectangleCorner f.hs choice
      (fwWideRectangle f.hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)), 0)) : ℝ) -
     ((entry reference (packedRectangleCorner f.hs choice
      (fwWideRectangle f.hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)), 0)) : ℝ) +
      (entry reference (packedRectangleCorner f.hs choice
      (fwWideRectangle f.hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)), 1)) : ℝ))/2)) =
    -(1/2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n side,
      (let block := f.blocks.get (Fin.cast f.hlen.symm (finProdFinEquiv (j, f.πw j b))); (block.high₁ : ℝ) - (block.low₁ : ℝ))


  reference_growth_row : ∀ r : Fin n,
    let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) f.hoff f.hs choice f.gr f.gc f.hgr f.hgc
    let μ := fun j : Fin f.stages.length =>
      (∑ p ∈ (f.stages.get j).lows, growthStageMidpoint (f.stages.get j) p) / (6*(n+8) : ℕ)
    |∑ s : Fin f.stages.length × Fin (6*(n+8)), physicalPairLineWeight growth (fun c => c.1 = r) s *
      ((((entry reference (growth (s,true)) : ℝ) + entry reference (growth (s,false))) / 2) - μ s.1)| ≤
      (Nat.clog 2 (6*n) : ℝ) * (8*((poolMaximum n : ℝ)/6)) +
        3*((poolMaximum n : ℝ)/6)/(n : ℝ) + 2*((poolMaximum n : ℝ)/6)
  reference_growth_col : ∀ c : Fin n,
    let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) f.hoff f.hs choice f.gr f.gc f.hgr f.hgc
    let μ := fun j : Fin f.stages.length =>
      (∑ p ∈ (f.stages.get j).lows, growthStageMidpoint (f.stages.get j) p) / (6*(n+8) : ℕ)
    |∑ s : Fin f.stages.length × Fin (6*(n+8)), physicalPairLineWeight growth (fun q => q.2 = c) s *
      ((((entry reference (growth (s,true)) : ℝ) + entry reference (growth (s,false))) / 2) - μ s.1)| ≤
      (Nat.clog 2 (6*n) : ℝ) * (8*((poolMaximum n : ℝ)/6)) +
        3*((poolMaximum n : ℝ)/6)/(n : ℝ) + 2*((poolMaximum n : ℝ)/6)
  reference_early : ∀ l : Fin ((n+n)+2),
    let cells := fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc
    let line := fun c => c ∈ physicalAllLineCells l
    let weights := fun j q => physicalPairLineWeight cells line (j,q)
    let values := fun j q => (((entry f.grown (cells ((j,q),false)) : ℝ) +
      entry f.grown (cells ((j,q),true))) / 2)
    |∑ j, ∑ i, weights j i *
      ((((entry reference (cells ((j,i),false)) : ℝ) + entry reference (cells ((j,i),true))) / 2) -
        ((∑ q, values j q) / (6*(n+8) : ℕ)))| ≤
      Real.sqrt (((11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2) * Real.log (4 * (((n+n)+2 : ℕ) : ℝ)) / 2) ∧
    |doubleBlockActualCenteredScore (fwBridgePhysicalDoubleCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc)
      line f.source reference| < (poolMaximum n : ℝ) * (23 / 924 : ℝ) * Real.sqrt (94 * Real.log (8 * (n : ℝ) + 8)) ∧
    |doubleBlockActualCenteredScore (fwWidePhysicalDoubleCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc)
      line f.source reference| < (poolMaximum n : ℝ) * (2 / 235 : ℝ) *
        Real.sqrt ((54 * ((n / 450 : ℕ) : ℝ) + 4) * Real.log (8 * (n : ℝ) + 8))

theorem fw_theta_projected_fresh_wide_witness
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
           (∑ p, physicalPairLineOrientation cells (line l) p * ((2 : ℝ) / 2))| ≤ B) ∧
       ∃ (T U V : Fin stages.length → Finset ℕ)
         (τ : Fin stages.length → Equiv.Perm (Fin (6 * (n + 8))))
         (final : Cell n ≃ Fin (n*n)),
         (∀ j, T j ⊆ (stages.get j).lows ∧ U j ⊆ (stages.get j).lows \ T j ∧
           V j ⊆ (stages.get j).lows \ (T j ∪ U j) ∧
           (T j).card = 12 ∧ (U j).card = 12 ∧ (V j).card = 24) ∧
         (∀ j, (fwGrowthMainSlots n).image (fun i => trace.lowAt rfl j (τ j i)) = T j ∧
           (fwGrowthAntiSlots n).image (fun i => trace.lowAt rfl j (τ j i)) = U j ∧
           (fwGrowthPartnerSlots n).image (fun i => trace.lowAt rfl j (τ j i)) = V j) ∧
         (∀ x, entry final (growth x) =
           (trace.poolValues rfl (by intro v hv; exact mem_poolFinset.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1)
             (stagePairPermutation τ x)).val) ∧
         (∀ c, c ∉ Set.range growth → entry final c = entry new c) ∧
         (∀ x, entry final (cells x) = entry new (cells x)) ∧
         (∀ x, entry final (bridge x) = entry new (bridge x)) ∧
         (∀ x, entry final (wide x) = entry new (wide x)) ∧
      (∀ j side, (∑ r : Fin 12,
        ((entry final (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0)) : ℝ) -
         ((entry final (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0)) : ℝ) +
          (entry final (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),1)) : ℝ))/2)) =
        -(1/2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n side,
          (let block := blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,πw j b))); (block.high₁ : ℝ) - (block.low₁ : ℝ))) ∧
            (∀ j, Finset.univ.image (fun x : Fin (6*(n+8)) × Bool => entry final (growth ((j,x.1),x.2))) =
           Finset.univ.image (fun x : Fin (6*(n+8)) × Bool => entry new (growth ((j,x.1),x.2)))) ∧
         (∀ j i, entry final (growth ((j,i),true)) = entry final (growth ((j,i),false)) + (stages.get j).gap) ∧
         ((∑ c ∈ (Finset.univ.image growth).filter (fun c => c ∈ mainCells n), (entry final c : ℝ)) =
           (∑ j, ∑ p ∈ T j, growthStageMidpoint (stages.get j) p) - 6 * ∑ j, ((stages.get j).gap : ℝ)) ∧
         ((∑ c ∈ (Finset.univ.image growth).filter (fun c => c ∈ antiCells n), (entry final c : ℝ)) =
           (∑ j, ∑ p ∈ U j, growthStageMidpoint (stages.get j) p) - 6 * ∑ j, ((stages.get j).gap : ℝ)) ∧
         (∀ l, |doubleBlockActualCenteredScore bridge (line l) b final| <
           (poolMaximum n : ℝ) * (23 / 924 : ℝ) * Real.sqrt (94 * Real.log (8 * (n : ℝ) + 8))) ∧
         (∀ l, |doubleBlockActualCenteredScore wide (line l) b final| <
           (poolMaximum n : ℝ) * (2 / 235 : ℝ) *
             Real.sqrt ((54 * ((n / 450 : ℕ) : ℝ) + 4) * Real.log (8 * (n : ℝ) + 8))) ∧
         (∀ l, |(∑ c ∈ (Finset.univ.image cells).filter (line l), (entry final c : ℝ)) -
           (∑ j, ((∑ q, weights l j q) * ((∑ q, values j q) / ((6 * (n + 8) : ℕ) : ℝ)))) -
           (∑ p, physicalPairLineOrientation cells (line l) p * ((2 : ℝ) / 2))| ≤ B) ∧
         (let μ := fun j => (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) / (6*(n+8) : ℕ)
          let E1 := (∑ j, ∑ p ∈ T j, growthStageMidpoint (stages.get j) p) - (12:ℝ) * ∑ j, μ j
          let D2 := (∑ j, ∑ p ∈ U j, growthStageMidpoint (stages.get j) p) - (12:ℝ) * ∑ j, μ j
          let E2 := (∑ j, ∑ p ∈ T j ∪ U j, growthStageMidpoint (stages.get j) p) - (24:ℝ) * ∑ j, μ j
          let E3 := (∑ j, ∑ p ∈ (T j ∪ U j) ∪ V j, growthStageMidpoint (stages.get j) p) - (48:ℝ) * ∑ j, μ j
          |E1| ≤ ((poolMaximum n : ℝ)/6)/2 ∧
          |D2| ≤ ((n+8 : ℝ)/(2*(n+6)))*((poolMaximum n : ℝ)/6) ∧
          |E2| ≤ ((n+5 : ℝ)/(n+6))*((poolMaximum n : ℝ)/6) ∧
          |E3| ≤ (3/2:ℝ)*((poolMaximum n : ℝ)/6) ∧
          (0 < (poolMaximum n : ℝ)/6 → |E3| < (3/2:ℝ)*((poolMaximum n : ℝ)/6)) ∧
          |(∑ c ∈ (Finset.univ.image growth).filter (fun c => c ∈ mainCells n), (entry final c : ℝ)) -
            ((12:ℝ) * ∑ j, μ j - 6 * ∑ j, ((stages.get j).gap : ℝ))| ≤ ((poolMaximum n : ℝ)/6)/2 ∧
          |(∑ c ∈ (Finset.univ.image growth).filter (fun c => c ∈ antiCells n), (entry final c : ℝ)) -
            ((12:ℝ) * ∑ j, μ j - 6 * ∑ j, ((stages.get j).gap : ℝ))| ≤
              ((n+8 : ℝ)/(2*(n+6)))*((poolMaximum n : ℝ)/6) ∧
          (∀ r : Fin n,
            |∑ s : Fin stages.length × Fin (6*(n+8)),
              physicalPairLineWeight growth (fun c => c.1 = r) s *
                ((((entry final (growth (s,true)) : ℝ) + entry final (growth (s,false))) / 2) - μ s.1)| ≤
              (Nat.clog 2 (6*n) : ℝ) * (8*((poolMaximum n : ℝ)/6)) +
                3*((poolMaximum n : ℝ)/6)/(n : ℝ) + 2*((poolMaximum n : ℝ)/6)) ∧
          (∀ c : Fin n,
            |∑ s : Fin stages.length × Fin (6*(n+8)),
              physicalPairLineWeight growth (fun q => q.2 = c) s *
                ((((entry final (growth (s,true)) : ℝ) + entry final (growth (s,false))) / 2) - μ s.1)| ≤
              (Nat.clog 2 (6*n) : ℝ) * (8*((poolMaximum n : ℝ)/6)) +
                3*((poolMaximum n : ℝ)/6)/(n : ℝ) + 2*((poolMaximum n : ℝ)/6)))
         ∧ (let roleSet := fwGrowthEarlyRoleCells hrect hseedrect hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc ∪
              Finset.univ.image (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc)
    let allRows := ((rows ++ sr) ++ wr) ++ gr
    let allCols := ((cols ++ sc) ++ wc) ++ gc
    ∃ (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) allRows)
      (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
        (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport allRows)) allCols),
    let R := fun edge : Fin 3 × Fin n =>
      let destination : Fin (3 * (n + 8)) := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge
      last + (∑ j ∈ Finset.range 5, selectedBridgeGap batches (fwPermutedBridgeIndex πb destination j) j) +
        ∑ j, fwPermutedWideSourceGap blocks hlen πw j destination
    ∃ (hrowGap : ∀ i e, entry final ((allRows.get i).1 e, (allRows.get i).2 e) =
          entry final (e, (allRows.get i).2 e) + fwPhysicalRowLayerGap final allRows i e)
      (hcolGap : ∀ i e, entry final ((allCols.get i).2 e, (allCols.get i).1 e) =
          entry final ((allCols.get i).2 e, e) + fwPhysicalColumnLayerGap final allCols i e),
      let vrow := hrows.rowPairs final (fwPhysicalRowLayerGap final allRows) hrowGap
      let vcol := hcols.columnPairs final (fwPhysicalColumnLayerGap final allCols) hcolGap
      ∃ (BR : CenteredNetwork (Fin 3 × Fin n) (Fin allRows.length × Fin n) vrow)
        (BC : CenteredNetwork (Fin 3 × Fin n) (Fin allCols.length × Fin n) vcol),
        (∀ edge, BR.source edge = edge.2 ∧ BC.source edge = edge.2 ∧
          BR.target edge = p edge.1 edge.2 ∧ BC.target edge = p edge.1 edge.2) ∧
        (∀ edge, BR.block edge =
          (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
            (fun x => fwJointActualGridPairIndex rows sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2))) ∧
        (∀ edge, BC.block edge =
          (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
            (fun x => fwJointActualGridPairIndex cols sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2))) ∧
        (∀ edge, BR.radius edge = R edge ∧ BC.radius edge = R edge ∧
          2 * ((n / 450) * poolMaximum n) ≤ BR.radius edge) ∧
        ∃ b₀ : Cell n ≃ Fin (n*n),
          TwoNetworkReferenceInvoice final b₀ allRows allCols hrows hcols
            (fwPhysicalRowLayerGap final allRows) (fwPhysicalColumnLayerGap final allCols)
            hrowGap hcolGap BR BC ∧
          (∀ r, |2 * (rowSum b₀ r : ℤ) - physicalNetworkMidpointTwice vrow BR r| ≤ 9) ∧
          (∀ c, |2 * (columnSum b₀ c : ℤ) - physicalNetworkMidpointTwice vcol BC c| ≤ 9) ∧
          mainSum b₀ = mainSum final ∧ antiSum b₀ = antiSum final ∧
          (∀ c ∈ (packedRectangleSupport hs choice), entry b₀ c = entry final c) ∧
      (∀ j side, (∑ r : Fin 12,
        ((entry b₀ (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0)) : ℝ) -
         ((entry b₀ (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0)) : ℝ) +
          (entry b₀ (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),1)) : ℝ))/2)) =
        -(1/2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n side,
          (let block := blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,πw j b))); (block.high₁ : ℝ) - (block.low₁ : ℝ))) ∧
             (∀ c ∉ roleSet, entry b₀ c = entry final c) ∧
          (∀ k, entry b₀ (layerPairSlot allRows k false) + entry b₀ (layerPairSlot allRows k true) =
            entry final (layerPairSlot allRows k false) + entry final (layerPairSlot allRows k true)) ∧
          (∀ k, entry b₀ (layerPairSlot allCols k false).swap + entry b₀ (layerPairSlot allCols k true).swap =
            entry final (layerPairSlot allCols k false).swap + entry final (layerPairSlot allCols k true).swap) ∧
          (∀ j i, (((entry b₀ (growth ((j,i),false)) : ℝ) + entry b₀ (growth ((j,i),true))) / 2) =
            (((entry final (growth ((j,i),false)) : ℝ) + entry final (growth ((j,i),true))) / 2)) ∧
          (let μ := fun j => (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) / (6*(n+8) : ℕ)
           (∀ r : Fin n,
             |∑ s : Fin stages.length × Fin (6*(n+8)),
               physicalPairLineWeight growth (fun c => c.1 = r) s *
                 ((((entry b₀ (growth (s,true)) : ℝ) + entry b₀ (growth (s,false))) / 2) - μ s.1)| ≤
               (Nat.clog 2 (6*n) : ℝ) * (8*((poolMaximum n : ℝ)/6)) +
                 3*((poolMaximum n : ℝ)/6)/(n : ℝ) + 2*((poolMaximum n : ℝ)/6)) ∧
           (∀ c : Fin n,
             |∑ s : Fin stages.length × Fin (6*(n+8)),
               physicalPairLineWeight growth (fun q => q.2 = c) s *
                 ((((entry b₀ (growth (s,true)) : ℝ) + entry b₀ (growth (s,false))) / 2) - μ s.1)| ≤
               (Nat.clog 2 (6*n) : ℝ) * (8*((poolMaximum n : ℝ)/6)) +
                 3*((poolMaximum n : ℝ)/6)/(n : ℝ) + 2*((poolMaximum n : ℝ)/6))) ∧
          (∀ l : Fin ((n+n)+2),
            |(∑ j, ∑ i, weights l j i *
              (((((entry b₀ (cells ((j,i),false)) : ℝ) + entry b₀ (cells ((j,i),true))) / 2)) -
                ((∑ q, values j q) / (6*(n+8) : ℕ))))| ≤ B ∧
            |doubleBlockActualCenteredScore bridge (line l) b b₀| <
              (poolMaximum n : ℝ) * (23 / 924 : ℝ) * Real.sqrt (94 * Real.log (8 * (n : ℝ) + 8)) ∧
            |doubleBlockActualCenteredScore wide (line l) b b₀| <
              (poolMaximum n : ℝ) * (2 / 235 : ℝ) *
                Real.sqrt ((54 * ((n / 450 : ℕ) : ℝ) + 4) * Real.log (8 * (n : ℝ) + 8))) ∧
          roleSet.image (entry b₀) = roleSet.image (entry final) ∧
          Set.range (entry b₀) = pool n ∧ Function.Injective (entry b₀) ∧
          (∀ fr : Fin 3 × Fin n → ℤ,
          (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fr e ∧
            fr e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
          ∀ fc : Fin 3 × Fin n → ℤ,
          (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fc e ∧
            fc e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
          ∃ b : Cell n ≃ Fin (n*n),
            (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
              2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fr e r) ∧
            (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) =
              2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fc e c) ∧
            mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
            (∀ c ∈ (packedRectangleSupport hs choice), entry b c = entry b₀ c) ∧
            (∀ c ∉ roleSet, entry b c = entry final c) ∧
            roleSet.image (entry b) = roleSet.image (entry final) ∧
            Set.range (entry b) = pool n ∧ Function.Injective (entry b)) ∧
          ∃ (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
            (w : FWThetaRoleValueInputs f seeds),
            f.stages = stages ∧ f.blocks = blocks ∧ f.batches = batches ∧
            f.br = rows ∧ f.bc = cols ∧ f.sr = sr ∧ f.sc = sc ∧
            f.wr = wr ∧ f.wc = wc ∧ f.gr = gr ∧ f.gc = gc ∧
            f.initial = initial ∧ f.stock = stock ∧ f.last = last ∧ HEq f.trace trace ∧
            f.source = b ∧ f.grown = grown ∧ f.ordered = final ∧
            f.πb = πb ∧ f.sb = (fun j k => sb (j,k)) ∧
            f.πw = πw ∧ f.sw = (fun j k => sw (j,k)) ∧
            f.gapb = (fun j k => (fwBridgeStageBlock n ∅ batches hvalid j (πb j k)).high₁ -
              (fwBridgeStageBlock n ∅ batches hvalid j (πb j k)).low₁) ∧
            f.gapw = (fun j k => let block := blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,πw j k))); block.high₁ - block.low₁) ∧
            f.ωseed = ω ∧ HEq f.τ τ ∧ w.intermediate = new ∧
            w.candidates = candidates ∧ w.kept = kept ∧
            Nonempty (FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs choice
              f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
              f.hrows f.hcols p f.ordered b₀ roleSet) ∧
            Nonempty (FWThetaGrowthDiagonalWitness n (fwJointRectangleCount n 254) choice f) ∧
            FWThetaFreshWideProjection f w.intermediate b₀
         )
         ) := by
  classical
  intro hrect hseedrect hwide hs hmax choice
  have hmain := bmor_fw_all_family_fresh_wide_gap_radius_upper_of_theta
    mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hprime hcount
  dsimp only at hmain ⊢
  refine hmain.imp fun p hp => ⟨hp.1, hp.2.1, ?_⟩
  refine hp.2.2.imp fun batches hbatches => hbatches.imp fun hvalid hcand0 => ?_
  refine hcand0.imp fun candidates hcand1 => hcand1.imp fun hcard hcand2 => ?_
  refine hcand2.imp fun kept hcand3 => hcand3.imp fun hsub hcand4 => ?_
  refine hcand4.imp fun hkept hcand5 => ⟨hcand5.1, ?_⟩
  have hcand := hcand5.1
  refine hcand5.2.imp fun rows hrows0 => hrows0.imp fun cols hcols0 => ?_
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
  refine ⟨hgrown.1, hgrown.2.1, hgrown.2.2.1, hgrown.2.2.2.1, hgrown.2.2.2.2.1,
    hgrown.2.2.2.2.2.1, hgrown.2.2.2.2.2.2.1, hgrown.2.2.2.2.2.2.2.1,
    hgrown.2.2.2.2.2.2.2.2.1, hgrown.2.2.2.2.2.2.2.2.2.1, ?_⟩
  have hcap := hgrown.1
  have hcross := hgrown.2.2.2.1
  have hupper := hgrown.2.2.2.2.1
  have hg1 := hgrown.2.2.2.2.2.2.2.2.2.2
  refine ⟨hg1.1, hg1.2.1, hg1.2.2.1, hg1.2.2.2.1, hg1.2.2.2.2.1, hg1.2.2.2.2.2.1,
    hg1.2.2.2.2.2.2.1, hg1.2.2.2.2.2.2.2.1, hg1.2.2.2.2.2.2.2.2.1, hg1.2.2.2.2.2.2.2.2.2.1, ?_⟩
  have hmatched := hg1.2.2.2.2.2.2.2.2.1
  refine hg1.2.2.2.2.2.2.2.2.2.2.imp fun ω hω => hω.imp fun b hb => ?_
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.1, ?_⟩
  have hset := hb.2.2.1
  have hbdB := hb.2.2.2.2.2.2.1
  have hboB := hb.2.2.2.2.2.2.2.1
  have hwpB := hb.2.2.2.2.2.2.2.2.1
  refine hb.2.2.2.2.2.2.2.2.2.imp fun πb hπb => hπb.imp fun sb hsb =>
    hsb.imp fun πw hπw => hπw.imp fun sw hsw => hsw.imp fun new hnew => ?_
  refine ⟨hnew.1, hnew.2.1, hnew.2.2.1, hnew.2.2.2.1, hnew.2.2.2.2.1,
    hnew.2.2.2.2.2.1, hnew.2.2.2.2.2.2.1, hnew.2.2.2.2.2.2.2.1,
    hnew.2.2.2.2.2.2.2.2.1, hnew.2.2.2.2.2.2.2.2.2.1, ?_⟩
  have hbe := hnew.1
  have hwe := hnew.2.1
  have hsetNew := hnew.2.2.2.2.2.1
  have hbstage := hnew.2.2.2.2.2.2.2.1
  have hwstage := hnew.2.2.2.2.2.2.2.2.1
  have hbgap := hnew.2.2.2.2.2.2.2.2.2.1
  have hn2 := hnew.2.2.2.2.2.2.2.2.2.2
  refine ⟨hn2.1, hn2.2.1, hn2.2.2.1, hn2.2.2.2.1, hn2.2.2.2.2.1, hn2.2.2.2.2.2.1,
    hn2.2.2.2.2.2.2.1, hn2.2.2.2.2.2.2.2.1, hn2.2.2.2.2.2.2.2.2.1, hn2.2.2.2.2.2.2.2.2.2.1, ?_⟩
  have hwgap := hn2.1
  have hside := hn2.2.2.2.2.1
  have hcenteredWide := hn2.2.2.2.2.2.1
  have hcontrast := hn2.2.2.2.2.2.2.1
  have hpermNew := hn2.2.2.2.2.2.2.2.1
  have hgapNew := hn2.2.2.2.2.2.2.2.2.1
  refine hn2.2.2.2.2.2.2.2.2.2.2.imp fun T hT => hT.imp fun U hU =>
    hU.imp fun V hV => hV.imp fun τ hτ => hτ.imp fun final hfinal => ?_
  refine ⟨hfinal.1, hfinal.2.1, hfinal.2.2.1, hfinal.2.2.2.1, hfinal.2.2.2.2.1,
    hfinal.2.2.2.2.2.1, hfinal.2.2.2.2.2.2.1, hfinal.2.2.2.2.2.2.2.1,
    hfinal.2.2.2.2.2.2.2.2.1, hfinal.2.2.2.2.2.2.2.2.2.1, ?_⟩
  have hsel2 := hfinal.1
  have hmap2 := hfinal.2.1
  have hperm2 := hfinal.2.2.1
  have hsf := hfinal.2.2.2.2.1
  have hbf := hfinal.2.2.2.2.2.1
  have hwf := hfinal.2.2.2.2.2.2.1
  have hfinalCentered := hfinal.2.2.2.2.2.2.2.1
  have hgap2 := hfinal.2.2.2.2.2.2.2.2.2.1
  have hf2 := hfinal.2.2.2.2.2.2.2.2.2.2
  refine ⟨hf2.1, hf2.2.1, hf2.2.2.1, hf2.2.2.2.1, hf2.2.2.2.2.1, hf2.2.2.2.2.2.1, ?_⟩
  have hmain2 := hf2.1
  have hanti2 := hf2.2.1
  have hfinalBridge := hf2.2.2.1
  have hfinalWide := hf2.2.2.2.1
  have hfinalSeed := hf2.2.2.2.2.1
  have hdiag := hf2.2.2.2.2.2.1
  have hE1 := hdiag.1
  have hD2 := hdiag.2.1
  have hE2 := hdiag.2.2.1
  have hE3 := hdiag.2.2.2.1
  have hE3s := hdiag.2.2.2.2.1
  have hbmain := hdiag.2.2.2.2.2.1
  have hbanti := hdiag.2.2.2.2.2.2.1
  have hrow := hdiag.2.2.2.2.2.2.2.1
  have hcol := hdiag.2.2.2.2.2.2.2.2
  refine hf2.2.2.2.2.2.2.imp fun hjointrow' hjr => hjr.imp fun hjointcol' hjc =>
    hjc.imp fun hrowGap hrg => hrg.imp fun hcolGap hcg =>
    hcg.imp fun BR hbr => hbr.imp fun BC hbc => ⟨hbc.1, hbc.2.1, hbc.2.2.1, hbc.2.2.2.1, ?_⟩
  have hends := hbc.1
  have hrowBlocks := hbc.2.1
  have hcolBlocks := hbc.2.2.1
  refine hbc.2.2.2.2.imp fun b₀ hb₀ => ?_
  refine ⟨hb₀.1, hb₀.2.1, hb₀.2.2.1, hb₀.2.2.2.1, hb₀.2.2.2.2.1, hb₀.2.2.2.2.2.1,
    hb₀.2.2.2.2.2.2.1, hb₀.2.2.2.2.2.2.2.1, hb₀.2.2.2.2.2.2.2.2.1, hb₀.2.2.2.2.2.2.2.2.2.1,
    hb₀.2.2.2.2.2.2.2.2.2.2.1, hb₀.2.2.2.2.2.2.2.2.2.2.2.1, hb₀.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hb₀.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hb₀.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hb₀.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hb₀.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, ?_⟩
  have hinvoice := hb₀.1
  have hmidrow := hb₀.2.1
  have hmidcol := hb₀.2.2.1
  have hmain := hb₀.2.2.2.1
  have hanti := hb₀.2.2.2.2.1
  have hrectfixed := hb₀.2.2.2.2.2.1
  have hreferenceCentered := hb₀.2.2.2.2.2.2.1
  have houtside := hb₀.2.2.2.2.2.2.2.1
  have hrow₀ := hb₀.2.2.2.2.2.2.2.2.2.2.2.1.1
  have hcol₀ := hb₀.2.2.2.2.2.2.2.2.2.2.2.1.2
  have hearly := hb₀.2.2.2.2.2.2.2.2.2.2.2.2.1
  have himage := hb₀.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpool₀ := hb₀.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hinj := hb₀.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hflows := hb₀.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  let initial := ((poolFinset n).filter (fun p => 43 < p)) \
    fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
  have hpool : ∀ p ∈ initial, p ∈ pool n := by
    intro v hv
    exact mem_poolFinset.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
  let gapb := fun j k => (fwBridgeStageBlock n ∅ batches hvalid j (πb j k)).high₁ -
    (fwBridgeStageBlock n ∅ batches hvalid j (πb j k)).low₁
  let gapw := fun j k =>
    let block := blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,πw j k)))
    block.high₁ - block.low₁
  let f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice := {
    stages := stages, stageCap := hcap, hrect := hrect, hseedrect := hseedrect, hwide := hwide,
    hoff := hoff, hs := hs, br := rows, bc := cols, sr := sr, sc := sc, wr := wr, wc := wc,
    gr := gr, gc := gc, hbr := hr, hbc := hc, hsr := hsr, hsc := hsc, hwr := hwr, hwc := hwc,
    hgr := hgr, hgc := hgc, hrows := hjointrow', hcols := hjointcol', source := b, grown := grown,
    ordered := final, batches := batches, hvalid := hvalid, blocks := blocks, hlen := hlen,
    hdiag := hbdB, hord := hboB, hplaced := hwpB, hmatched := hmatched,
    πb := πb, sb := fun j k => sb (j,k), πw := πw, sw := fun j k => sw (j,k),
    hbridge := by
      intro j k q side
      exact (hbf ((j,k,q),side)).trans (hbe j k q side),
    hwideEntry := by
      intro j k q side
      exact (hwf ((j,k,q),side)).trans (hwe j k q side),
    gapb := gapb, gapw := gapw,
    hinvoiceb := by
      intro j k q
      rw [hbf ((j,k,q),true), hbf ((j,k,q),false)]
      exact hbgap j k q,
    hinvoicew := by
      intro j k q
      rw [hwf ((j,k,q),true), hwf ((j,k,q),false)]
      exact hwgap j k q,
    hpairgap := hgap2,
    hseedgap := by
      intro j i
      rw [hsf ((j,i),true), hsf ((j,i),false)]
      exact hgapNew j i,
    hBridgeScore := hfinalBridge, hWideScore := hfinalWide,
    initial := initial, stock := stock, last := last, trace := trace, hpool := hpool,
    ωseed := ω, τ := τ,
    hseedPlace := by
      intro j i side
      exact (hsf ((j,i),side)).trans (hpermNew j i side),
    hgrowthPlace := hperm2, hseedScore := hfinalSeed, hgrowthRow := hrow, hgrowthCol := hcol }
  let w : FWThetaRoleValueInputs f seeds := {
      candidates := candidates
      candidate_card := hcard
      kept := kept
      kept_sub := hsub
      kept_card := hkept
      candidates_sub := hcand
      initial_eq := rfl
      intermediate := new
      seed_base := hset
      bridge_stage := hbstage
      wide_stage := hwstage
      seed_intermediate := hsetNew
      bridge_final := hbf
      wide_final := hwf
      seed_final := hsf
    }
  refine ⟨f, w, ?_⟩
  repeat' first | apply And.intro | rfl
  · refine ⟨?_⟩
    exact {
      roles_eq := rfl
      row_gap := hrowGap
      col_gap := hcolGap
      row_network := BR
      col_network := BC
      endpoints := hends
      row_blocks := hrowBlocks
      col_blocks := hcolBlocks
      invoice := hinvoice
      row_midpoint := hmidrow
      col_midpoint := hmidcol
      main_eq := hmain
      anti_eq := hanti
      rectangle_fixed := hrectfixed
      off_roles := houtside
      roles_image := himage
      old_pool := hpool₀
      old_injective := hinj
      flows := hflows
    }
  · refine ⟨?_⟩
    exact {
      T := T
      U := U
      V := V
      selected := hsel2
      slot_images := hmap2
      main_identity := hmain2
      anti_identity := hanti2
      midpoint_bounds := ⟨hE1, hD2, hE2, hE3, hE3s⟩
      main_deviation := hbmain
      anti_deviation := hbanti
    }
  · exact ⟨hcross, hupper, hside, hcenteredWide, hcontrast, hfinalCentered,
      hreferenceCentered, hrow₀, hcol₀, hearly⟩

end
end Sude
