import Sude.FWCompletedFirstBandAllLineFlows
import Sude.DQRFNetworkCompletionJoin

/-! Given the exact selected theta-style witness fields and explicit widened
DQ/RF premises, construct one completion and synchronized reference, retaining
all physical line bounds and bounded flow outputs. This does not extract a
monolithic theta witness, discharge numerical/stock premises, or prove prime
lines, a final threshold, or later-flow absolute bounds. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

theorem fw_given_theta_witness_dqrf_all_line_flows
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} {stages : List BTSelectedStage} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hP : stages.length ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseedrect : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + stages.length * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n) (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (source ordered oldReference : Cell n ≃ Fin (n*n))
    (initial : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (hdiag : ∀ t side, entry source (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (hord : ∀ x, entry source (fwBridgeLayerCells br bc hbr hbc x) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeOrdinarySlot n x))
    (hplaced : ∀ x : FWWideInputs n, entry source (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))
        (fwReflectedRight (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n)))
      (bmorHighBins (fwReflectedLeft (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))
        (fwReflectedRight (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))))
    (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8)))) (sb : Fin 5 → Fin (3 * (n + 8)) → Bool)
    (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (sw : Fin (3 * (n / 450)) → Fin (3 * (n + 8)) → Bool)
    (hbridge : ∀ j b p side, entry ordered (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,b,p),side)) =
      entry source (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,πb j b,doubleBlockPairSwap (sb j b) p),side)))
    (hwideEntry : ∀ j b p side, entry ordered (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),side)) =
      entry source (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,πw j b,doubleBlockPairSwap (sw j b) p),side)))
    (hpairgap : ∀ j i, entry ordered (btGrowingOffsetPairCells
      (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc ((j,i),true)) =
      entry ordered (btGrowingOffsetPairCells
        (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc ((j,i),false)) + (stages.get j).gap)
    (hseedgap : ∀ j q, entry ordered (fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc ((j,q),true)) =
       entry ordered (fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc ((j,q),false)) + 2)
    (vr : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) ordered)
    (vc : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) (LayerPacking.transposePlacement ordered))
    (networkR : CenteredNetwork (Fin 3 × Fin n) (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) vr)
    (networkC : CenteredNetwork (Fin 3 × Fin n) (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) vc)
    (hslotr : ∀ t side, rowNetworkSlot vr (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (hslotc : ∀ t side, rowNetworkSlot vc (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side)
    (hblockr : ∀ edge, networkR.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2)))
    (hblockc : ∀ edge, networkC.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex bc sc wc gc hbc hsc hwc hgc ((x,edge.1),edge.2)))
    (roles : Finset (Cell n))
    (hroles : roles = fwGrowthEarlyRoleCells hrect hseedrect hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc))
    (hoffactive : ∀ x ∉ roles, entry oldReference x = entry ordered x)
    (himage : roles.image (entry oldReference) = roles.image (entry ordered))
    (hmain : mainSum oldReference = mainSum ordered)
    (hanti : antiSum oldReference = antiSum ordered)
    (hinvrow : ∀ r, |2 * (rowSum oldReference r : ℤ) - physicalNetworkMidpointTwice vr networkR r| ≤ 9)
    (hinvcol : ∀ j, |2 * (columnSum oldReference j : ℤ) - physicalNetworkMidpointTwice vc networkC j| ≤ 9)
    (gapb : Fin 5 → Fin (3 * (n + 8)) → ℕ)
    (gapw : Fin (3 * (n / 450)) → Fin (3 * (n + 8)) → ℕ)
    (hinvoiceb : ∀ j b p,
      entry ordered (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,b,p),true)) =
      entry ordered (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,b,p),false)) + gapb j b)
    (hinvoicew : ∀ j b p,
      entry ordered (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),true)) =
      entry ordered (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),false)) + gapw j b)
    (B W U V : ℝ)
    (hBr : ∀ r : Fin n, |doubleBlockActualCenteredScore (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
      (fun z => z ∈ (rowCells r)) source ordered| ≤ B)
    (hWr : ∀ r : Fin n, |doubleBlockActualCenteredScore (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
      (fun z => z ∈ (rowCells r)) source ordered| ≤ W)
    (hseedr : ∀ r : Fin n,
      let cells := fwFourFamilyPairCells hrect hseedrect hwide hoff hs choice
        br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n stages.length
      let mean := fun j : FWFourStageIndex n stages.length =>
        (∑ i, (((entry ordered (cells ((j,i),false)) : ℝ) + entry ordered (cells ((j,i),true))) / 2)) /
          ((6 * (n + 8) : ℕ) : ℝ)
      let seed := fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc
      |(∑ z ∈ (rowCells r) ∩ Finset.univ.image seed, (entry ordered z : ℝ)) -
        (∑ j : Fin 16, ∑ i : Fin (6*(n+8)), physicalPairLineWeight seed (fun z => z ∈ (rowCells r)) (j,i) *
          mean (Sum.inl (Sum.inl (Sum.inr j))))| ≤ U)
    (hgrowthr : ∀ r : Fin n,
      let cells := fwFourFamilyPairCells hrect hseedrect hwide hoff hs choice
        br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n stages.length
      let mean := fun j : FWFourStageIndex n stages.length =>
        (∑ i, (((entry ordered (cells ((j,i),false)) : ℝ) + entry ordered (cells ((j,i),true))) / 2)) /
          ((6 * (n + 8) : ℕ) : ℝ)
      let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc
      |(∑ z ∈ (rowCells r) ∩ Finset.univ.image growth, (entry ordered z : ℝ)) -
        (∑ j : Fin stages.length, ∑ i : Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z ∈ (rowCells r)) (j,i) * mean (Sum.inr j))| ≤ V)
    (hBc : ∀ c : Fin n, |doubleBlockActualCenteredScore (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
      (fun z => z ∈ (columnCells c)) source ordered| ≤ B)
    (hWc : ∀ c : Fin n, |doubleBlockActualCenteredScore (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
      (fun z => z ∈ (columnCells c)) source ordered| ≤ W)
    (hseedc : ∀ c : Fin n,
      let cells := fwFourFamilyPairCells hrect hseedrect hwide hoff hs choice
        br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n stages.length
      let mean := fun j : FWFourStageIndex n stages.length =>
        (∑ i, (((entry ordered (cells ((j,i),false)) : ℝ) + entry ordered (cells ((j,i),true))) / 2)) /
          ((6 * (n + 8) : ℕ) : ℝ)
      let seed := fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc
      |(∑ z ∈ (columnCells c) ∩ Finset.univ.image seed, (entry ordered z : ℝ)) -
        (∑ j : Fin 16, ∑ i : Fin (6*(n+8)), physicalPairLineWeight seed (fun z => z ∈ (columnCells c)) (j,i) *
          mean (Sum.inl (Sum.inl (Sum.inr j))))| ≤ U)
    (hgrowthc : ∀ c : Fin n,
      let cells := fwFourFamilyPairCells hrect hseedrect hwide hoff hs choice
        br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n stages.length
      let mean := fun j : FWFourStageIndex n stages.length =>
        (∑ i, (((entry ordered (cells ((j,i),false)) : ℝ) + entry ordered (cells ((j,i),true))) / 2)) /
          ((6 * (n + 8) : ℕ) : ℝ)
      let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc
      |(∑ z ∈ (columnCells c) ∩ Finset.univ.image growth, (entry ordered z : ℝ)) -
        (∑ j : Fin stages.length, ∑ i : Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z ∈ (columnCells c)) (j,i) * mean (Sum.inr j))| ≤ V)
    {bits : ℕ} (ε : ℝ)
    (full : Finset (Cell n))
    (hfull : full = packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc)))
    (Dold : ℕ) (hε : 0 ≤ ε) (hodd : Odd n) (hcenter : centralCell n (by omega) ∉ full)
    (hreserve : 4 * full.card ≤ n*n)
    (hload : 4 * (12*(5+16+3*(n/450)+stages.length) + 6*bits + 4) ≤ n)
    (hrowlo : ∀ i, 12*(5+16+3*(n/450)+stages.length) ≤ (LayerPacking.rowUsed (full ∪ unreservedDiagonalCells full) i).card)
    (hrowhi : ∀ i, (LayerPacking.rowUsed (full ∪ unreservedDiagonalCells full) i).card ≤ 12*(5+16+3*(n/450)+stages.length) + (6*bits+4))
    (hcollo : ∀ i, 12*(5+16+3*(n/450)+stages.length) ≤ (LayerPacking.colUsed (full ∪ unreservedDiagonalCells full) i).card)
    (hcolhi : ∀ i, (LayerPacking.colUsed (full ∪ unreservedDiagonalCells full) i).card ≤ 12*(5+16+3*(n/450)+stages.length) + (6*bits+4))
    (hleft : 1 ≤ centralEntriesMean (actualUnusedPool ordered full) centralPoolValue - ε * poolMaximum n -
      3 * (poolMaximum n : ℝ) / (4*n))
    (hright : centralEntriesMean (actualUnusedPool ordered full) centralPoolValue + ε * poolMaximum n +
      3 * (poolMaximum n : ℝ) / (4*n) ≤ poolMaximum n)
    (hdeleted : (apInterval
      (centralEntriesMean (actualUnusedPool ordered full) centralPoolValue - ε * poolMaximum n - 3 * (poolMaximum n : ℝ) / (4*n))
      (centralEntriesMean (actualUnusedPool ordered full) centralPoolValue + ε * poolMaximum n + 3 * (poolMaximum n : ℝ) / (4*n))
      2 1 ∩ full.image (entry ordered)).card ≤ Dold)
    (hgate : (((9 * bits + 6) * n : ℕ) : ℝ) ≤
      (2 * (ε * poolMaximum n) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n)) /
        Real.log (poolMaximum n) - (((Dold + (2*n - 1) : ℕ)) : ℝ))
    (p : Fin 3 → Equiv.Perm (Fin n))
    (hflows : ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
      ∃ b : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum b r : ℤ) - (rowSum oldReference r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fr e r) ∧
        (∀ j, (columnSum b j : ℤ) - (columnSum oldReference j : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fc e j) ∧
        mainSum b = mainSum oldReference ∧ antiSum b = antiSum oldReference ∧
        (∀ z ∈ packedRectangleSupport hs choice, entry b z = entry oldReference z) ∧
        (∀ z ∉ roles, entry b z = entry ordered z) ∧
        roles.image (entry b) = roles.image (entry ordered) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b)) :
    ∃ (diagonal completed reference : Cell n ≃ Fin (n*n)),
      (∀ z ∈ full, entry diagonal z = entry ordered z) ∧
      (∀ z ∈ full ∪ unreservedDiagonalCells full, entry completed z = entry diagonal z) ∧
      (∀ z ∈ full, entry completed z = entry ordered z) ∧
      (∀ z ∈ roles, entry reference z = entry oldReference z) ∧
      (∀ z ∉ roles, entry reference z = entry completed z) ∧
      |(mainSum completed : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry ordered z : ℝ)) +
        ((mainCells n \ full).card : ℝ) * centralEntriesMean (actualUnusedPool ordered full) centralPoolValue)| ≤
          (poolMaximum n : ℝ) ∧
      |(antiSum completed : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry ordered z : ℝ)) +
        ((antiCells n \ full).card : ℝ) * centralEntriesMean (actualUnusedPool ordered full) centralPoolValue)| ≤
          (3/2 : ℝ) * poolMaximum n ∧
      (∀ i, |(rowSum completed i : ℝ) - ((∑ z ∈ rowCells i ∩ full, (entry ordered z : ℝ)) +
        ((rowCells i \ full).card : ℝ) * centralEntriesMean (actualUnusedPool ordered full) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) ∧
      (∀ i, |(columnSum completed i : ℝ) - ((∑ z ∈ columnCells i ∩ full, (entry ordered z : ℝ)) +
        ((columnCells i \ full).card : ℝ) * centralEntriesMean (actualUnusedPool ordered full) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) ∧
      2*n ≤ (actualUnusedPool diagonal (full ∪ unreservedDiagonalCells full)).card ∧
      |centralEntriesMean (actualUnusedPool diagonal (full ∪ unreservedDiagonalCells full)) centralPoolValue -
        centralEntriesMean (actualUnusedPool ordered full) centralPoolValue| ≤ 3 * (poolMaximum n : ℝ) / (4*n) ∧
      mainSum completed = mainSum diagonal ∧ antiSum completed = antiSum diagonal ∧
      mainSum reference = mainSum completed ∧ antiSum reference = antiSum completed ∧
      Set.range (entry completed) = pool n ∧ Function.Injective (entry completed) ∧
    (∀ r, |(rowSum reference r : ℝ) - (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| < ((9 : ℝ) / 2 + B + W + U + V +
        (257 / 250 : ℝ) * poolMaximum n + (19033 / 450 : ℝ) * (201 / 10000 : ℝ) * poolMaximum n) +
        ((1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n)) ∧
    (∀ c, |(columnSum reference c : ℝ) - (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| < ((9 : ℝ) / 2 + B + W + U + V +
        (257 / 250 : ℝ) * poolMaximum n + (19033 / 450 : ℝ) * (201 / 10000 : ℝ) * poolMaximum n) +
        ((1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n)) ∧
    (∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
      ∃ b b' : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum b r : ℤ) - (rowSum oldReference r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fr e r) ∧
        (∀ j, (columnSum b j : ℤ) - (columnSum oldReference j : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fc e j) ∧
        mainSum b = mainSum oldReference ∧ antiSum b = antiSum oldReference ∧
        (∀ z ∈ packedRectangleSupport hs choice, entry b z = entry oldReference z) ∧
        (∀ z ∉ roles, entry b z = entry ordered z) ∧
        roles.image (entry b) = roles.image (entry ordered) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) ∧
        (∀ z ∈ roles, entry b' z = entry b z) ∧
        (∀ z ∉ roles, entry b' z = entry completed z) ∧
        (∀ r, (rowSum b' r : ℤ) - (rowSum reference r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fr e r) ∧
        (∀ j, (columnSum b' j : ℤ) - (columnSum reference j : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fc e j) ∧
        mainSum b' = mainSum reference ∧ antiSum b' = antiSum reference ∧
        (∀ z ∈ packedRectangleSupport hs choice, entry b' z = entry reference z) ∧
        roles.image (entry b') = roles.image (entry completed) ∧
        Set.range (entry b') = pool n ∧ Function.Injective (entry b')) := by
  classical
  have hgeom := fw_role_support_for_trace_networks hP hrect hseedrect hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  dsimp only at hgeom
  have hsub : roles ⊆ full := by
    rw [hroles, hfull]
    exact hgeom.2.2.1
  have hrowSlots : ∀ k side, rowNetworkSlot vr (k,side) ∈ roles := by
    intro k side
    rw [hslotr, hroles]
    exact hgeom.1 (layerPairSlot_mem _ k side)
  have hcolSlots : ∀ k side, (rowNetworkSlot vc (k,side)).swap ∈ roles := by
    intro k side
    rw [hslotc, hroles]
    exact hgeom.2.1 (transposedLayerPairSlot_mem _ k side)
  obtain ⟨diagonal, completed, reference, hdiagfix, hcdiagfix, hfixedfull, hmainDiag, hantiDiag,
    hcompletionr, hcompletionc, hstock, hshift, hcmain, hcanti, hpool, hinj,
    hdactive, hdoff, hdmain, hdanti, hr, hc, hinvrow', hinvcol'⟩ :=
    dq_rf_network_completion_join bmor upper ordered oldReference full roles ε Dold hε (by omega) (by omega)
      hodd hcenter hreserve hload hrowlo hrowhi hcollo hcolhi hleft hright hdeleted hgate
      vr networkR vc networkC hsub hoffactive himage hmain hanti hrowSlots hcolSlots hinvrow hinvcol
  have hfixed : ∀ z ∈ packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc)), entry completed z = entry ordered z := by
    intro z hz
    apply hfixedfull z
    rwa [hfull]
  have hr' := hcompletionr
  have hc' := hcompletionc
  rw [hfull] at hr' hc'
  have hall := fw_completed_first_band_all_line_flows bmor lower upper hnlo hnhi hP
    hrect hseedrect hwide hoff hs choice br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
    source ordered completed oldReference reference hfixed initial batches hvalid blocks hlen hdiag hord hplaced hmatched
    πb sb πw sw hbridge hwideEntry hpairgap hseedgap vr vc networkR networkC hslotr hslotc hblockr hblockc
    roles hroles hoffactive himage hdactive hdoff hmain hanti hinvrow hinvcol
    gapb gapw hinvoiceb hinvoicew B W U V hBr hWr hseedr hgrowthr hBc hWc hseedc hgrowthc ε hr' hc'
    full hfull (packedRectangleSupport hs choice) p ((n / 450) * poolMaximum n) hflows
  exact ⟨diagonal, completed, reference, hdiagfix, hcdiagfix, hfixedfull, hdactive, hdoff,
    hmainDiag, hantiDiag, hcompletionr, hcompletionc, hstock, hshift, hcmain, hcanti,
    hdmain, hdanti, hpool, hinj, hall.1, hall.2.1, hall.2.2⟩

end
end Sude
