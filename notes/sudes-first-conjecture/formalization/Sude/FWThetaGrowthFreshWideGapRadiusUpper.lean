import Sude.FWThetaFreshWideGapRadiusUpper
import Sude.FWGrowthProtectedAllLineMidpoints

/-! A same-theta-witness growth allocation retaining seed, bridge, and wide
controls plus growth row/column midpoint and growth-image diagonal bounds.
This is not a complete-line theorem. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

theorem bmor_fw_growth_fresh_wide_gap_radius_upper_of_theta
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
                3*((poolMaximum n : ℝ)/6)/(n : ℝ) + 2*((poolMaximum n : ℝ)/6)))) := by
  classical
  intro hrect hseedrect hwide hs hmax choice
  have hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  have hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  have hQeq : 3 * (n + 8) * 2 = 6 * (n + 8) := by omega
  have hnpos : 3 ≤ n := by omega
  have hmain := bmor_fw_seed_bridge_wide_fresh_gap_radius_upper_of_theta
    mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hprime hcount
  dsimp only at hmain ⊢
  refine hmain.imp fun p hp => ⟨hp.1, hp.2.1, ?_⟩
  refine hp.2.2.imp fun batches hbatches => hbatches.imp fun hvalid hcand0 => ?_
  refine hcand0.imp fun candidates hcand1 => hcand1.imp fun hcard hcand2 => ?_
  refine hcand2.imp fun kept hcand3 => hcand3.imp fun hsub hcand4 => ?_
  refine hcand4.imp fun hkept hcand5 => ⟨hcand5.1, ?_⟩
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
  have hnarrow := hgrown.2.2.2.2.2.2.2.1
  have hg1 := hgrown.2.2.2.2.2.2.2.2.2.2
  refine ⟨hg1.1, hg1.2.1, hg1.2.2.1, hg1.2.2.2.1, hg1.2.2.2.2.1, hg1.2.2.2.2.2.1,
    hg1.2.2.2.2.2.2.1, hg1.2.2.2.2.2.2.2.1, hg1.2.2.2.2.2.2.2.2.1, hg1.2.2.2.2.2.2.2.2.2.1, ?_⟩
  have hjointrow := hg1.2.2.2.2.2.1
  have hjointcol := hg1.2.2.2.2.2.2.1
  have hplaced := hg1.2.2.2.2.2.2.2.1
  have hmatched := hg1.2.2.2.2.2.2.2.2.1
  refine hg1.2.2.2.2.2.2.2.2.2.2.imp fun ω hω => hω.imp fun b hb => ?_
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.1, ?_⟩
  refine hb.2.2.2.2.2.2.2.2.2.imp fun πb hπb => hπb.imp fun sb hsb =>
    hsb.imp fun πw hπw => hπw.imp fun sw hsw => hsw.imp fun new hnew => ?_
  refine ⟨hnew.1, hnew.2.1, hnew.2.2.1, hnew.2.2.2.1, hnew.2.2.2.2.1,
    hnew.2.2.2.2.2.1, hnew.2.2.2.2.2.2.1, hnew.2.2.2.2.2.2.2.1,
    hnew.2.2.2.2.2.2.2.2.1, hnew.2.2.2.2.2.2.2.2.2.1, ?_⟩
  have hgrowthRoleNew := hnew.2.2.2.2.1
  have hn2 := hnew.2.2.2.2.2.2.2.2.2.2
  refine ⟨hn2.1, hn2.2.1, hn2.2.2.1, hn2.2.2.2.1, hn2.2.2.2.2.1, hn2.2.2.2.2.2.1,
    hn2.2.2.2.2.2.2.1, hn2.2.2.2.2.2.2.2.1, hn2.2.2.2.2.2.2.2.2.1, hn2.2.2.2.2.2.2.2.2.2, ?_⟩
  have hbscore := hn2.2.2.1
  have hwscore := hn2.2.2.2.1
  have hcenteredWide := hn2.2.2.2.2.2.1
  have hselectedNew := hn2.2.2.2.2.2.2.2.2.2
  have hbal : ∀ j rect, choice (btGrowingOffsetRectangle
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff (finProdFinEquiv (j,rect))) =
        decide (rect.val < 12) := by
    intro j rect
    simpa [choice, fwBridgeSeedWideGrowthChoice, fwBridgeSeedWideRectangleChoice] using
      fwBridgeSeedWideGrowthChoice_offset_restrict hrect hseedrect hwide hmax hoff hcap otherChoice j rect
  let hpool : ∀ v ∈ ((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks, v ∈ pool n := by
    intro v hv
    exact mem_poolFinset.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
  have hinstalled : ∀ x : PrefixPhysicalInputs stages.length 6 3 n,
      entry new (btGrowingOffsetCells (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc x) =
        (trace.poolValues rfl hpool (prefixPhysicalInput hfit hdiag x)).val := by
    intro x
    exact (hgrowthRoleNew x).trans (hplaced x)
  obtain ⟨T,U,V,τ,final,hsel2,hmap2,hperm2,hfix2,hstage2,hgap2,hmain2,hanti2,
    hE1,hD2,hE2,hE3,hE3s,hbmain,hbanti,hrow,hcol,hsf,hbf,hwf,hbs,hws⟩ :=
    fw_growth_protected_all_line_midpoint_bounds trace hpool hnpos (poolMaximum n) (by positivity) hnarrow
      hcap hrect hseedrect hwide hoff hs choice rows cols sr sc wr wc gr gc
      hr hc hsr hsc hwr hwc hgr hgc hjointrow hjointcol hbal b new hinstalled
  let cells := fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc
  let line := fun l : Fin ((n+n)+2) => fun c => c ∈ physicalAllLineCells l
  let V₀ : ℝ := (11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2
  let B := Real.sqrt (V₀ * Real.log (4 * (((n+n)+2 : ℕ) : ℝ)) / 2)
  have hfinalSeed := seed_source_midpoint_concentration_preserved cells line grown new final B hsf hselectedNew
  have hfinalBridge : ∀ l, |doubleBlockActualCenteredScore
      (fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc) (line l) b final| <
      (poolMaximum n : ℝ) * (23 / 924 : ℝ) * Real.sqrt (94 * Real.log (8 * (n : ℝ) + 8)) := by
    intro l
    rw [hbs (line l)]
    exact hbscore l
  have hfinalWide : ∀ l, |doubleBlockActualCenteredScore
      (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) (line l) b final| <
      (poolMaximum n : ℝ) * (2 / 235 : ℝ) *
        Real.sqrt ((54 * ((n / 450 : ℕ) : ℝ) + 4) * Real.log (8 * (n : ℝ) + 8)) := by
    intro l
    rw [hws (line l)]
    exact hwscore l
  have hcorner : ∀ j side r (s : Bool),
      entry final (packedRectangleCorner hs choice
        (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),
          prefixPairCorner (0 : Fin 2) s)) =
      entry new (packedRectangleCorner hs choice
        (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),
          prefixPairCorner (0 : Fin 2) s)) := by
    intro j side r s
    have hh := hwf ((j, fwWideSignedGapSlot n side r, (0 : Fin 2)), s)
    have hc := fw_wide_reindexed_diagonal_cell hwide hs choice wr wc hwr hwc j
      (fwWideSignedGapRectangle side r) 0 s
    simp only [fw_wide_signed_gap_controller_index] at hc
    change entry final (fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc
      ((j, Fin.cast hQeq
        (finProdFinEquiv (fwWideSignedGapSlot n side r, (0 : Fin 2)))), s)) =
      entry new (fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc
      ((j, Fin.cast hQeq
        (finProdFinEquiv (fwWideSignedGapSlot n side r, (0 : Fin 2)))), s)) at hh
    rw [hc] at hh
    exact hh
  have hfinalNat : ∀ j side, (∑ r : Fin 12,
        ((entry final (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0)) : ℝ) -
         ((entry final (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0)) : ℝ) +
          (entry final (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),1)) : ℝ))/2)) =
        -(1/2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n side,
          (let block := blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,πw j b))); ((block.high₁ - block.low₁ : ℕ) : ℝ)) := by
    intro j side
    convert hcenteredWide j side using 1
    apply Finset.sum_congr rfl
    intro r _
    have h0 := hcorner j side r false
    have h1 := hcorner j side r true
    norm_num [prefixPairCorner] at h0 h1
    rw [h0, h1]
  have hgapReal : ∀ j k,
      (let block := blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,k)));
        ((block.high₁ - block.low₁ : ℕ) : ℝ)) =
      (let block := blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,k)));
        (block.high₁ : ℝ) - (block.low₁ : ℝ)) := by
    intro j k
    let idx := Fin.cast hlen.symm (finProdFinEquiv (j,k))
    let block := blocks.get idx
    have hm := hmatched block (List.get_mem blocks idx)
    have hord : block.low₁ ≤ block.high₁ := by
      rcases hm.1 with ⟨_, _, _, _, _, _, horder, _, _⟩
      exact Nat.le_of_lt horder
    exact Nat.cast_sub hord
  have hfinalCentered : ∀ j side, (∑ r : Fin 12,
        ((entry final (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0)) : ℝ) -
         ((entry final (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),0)) : ℝ) +
          (entry final (packedRectangleCorner hs choice
          (fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r)),1)) : ℝ))/2)) =
        -(1/2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n side,
          (let block := blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,πw j b))); (block.high₁ : ℝ) - (block.low₁ : ℝ)) := by
    intro j side
    rw [hfinalNat j side]
    apply congrArg (fun x : ℝ => -(1/2 : ℝ) * x)
    apply Finset.sum_congr rfl
    intro k hk
    exact hgapReal j (πw j k)
  exact ⟨T,U,V,τ,final,hsel2,hmap2,hperm2,hfix2,hsf,hbf,hwf,hfinalCentered,hstage2,hgap2,
    hmain2,hanti2,hfinalBridge,hfinalWide,hfinalSeed,hE1,hD2,hE2,hE3,hE3s,hbmain,hbanti,hrow,hcol⟩

end
end Sude
