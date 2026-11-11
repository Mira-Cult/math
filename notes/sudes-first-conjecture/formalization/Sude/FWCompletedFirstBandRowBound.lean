import Sude.FWFirstBandRowResidualBound
import Sude.FWCompletionFamilyInvariants
import Sude.FWCompletionSeedGrowthComponents
import Sude.FWGivenReferenceCompletionTransport
import Sude.CompletionRowResidualClosure

/-! Conditional same-witness physical row bound. The completion estimate and
all network, placement and analytic hypotheses are supplied. No construction,
final numerical threshold, primality or later-flow property is inferred. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

theorem fw_completed_first_band_row_bound
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
    (source ordered completed oldReference reference : Cell n ≃ Fin (n*n))
    (hfixed : ∀ z ∈ packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc)), entry completed z = entry ordered z)
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
    (hdactive : ∀ x ∈ roles, entry reference x = entry oldReference x)
    (hdoff : ∀ x ∉ roles, entry reference x = entry completed x)
    (hmain : mainSum oldReference = mainSum ordered)
    (hanti : antiSum oldReference = antiSum ordered)
    (hinvrow : ∀ r, |2 * (rowSum oldReference r : ℤ) - physicalNetworkMidpointTwice vr networkR r| ≤ 9)
    (hinvcol : ∀ j, |2 * (columnSum oldReference j : ℤ) - physicalNetworkMidpointTwice vc networkC j| ≤ 9)
    (r : Fin n)
    (B W U V : ℝ)
    (hB : |doubleBlockActualCenteredScore (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
      (fun z => z ∈ (rowCells r)) source ordered| ≤ B)
    (hW : |doubleBlockActualCenteredScore (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
      (fun z => z ∈ (rowCells r)) source ordered| ≤ W)
    (hseed :
      let cells := fwFourFamilyPairCells hrect hseedrect hwide hoff hs choice
        br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n stages.length
      let mean := fun j : FWFourStageIndex n stages.length =>
        (∑ i, (((entry ordered (cells ((j,i),false)) : ℝ) + entry ordered (cells ((j,i),true))) / 2)) /
          ((6 * (n + 8) : ℕ) : ℝ)
      let seed := fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc
      |(∑ z ∈ (rowCells r) ∩ Finset.univ.image seed, (entry ordered z : ℝ)) -
        (∑ j : Fin 16, ∑ i : Fin (6*(n+8)), physicalPairLineWeight seed (fun z => z ∈ (rowCells r)) (j,i) *
          mean (Sum.inl (Sum.inl (Sum.inr j))))| ≤ U)
    (hgrowth :
      let cells := fwFourFamilyPairCells hrect hseedrect hwide hoff hs choice
        br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n stages.length
      let mean := fun j : FWFourStageIndex n stages.length =>
        (∑ i, (((entry ordered (cells ((j,i),false)) : ℝ) + entry ordered (cells ((j,i),true))) / 2)) /
          ((6 * (n + 8) : ℕ) : ℝ)
      let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc
      |(∑ z ∈ (rowCells r) ∩ Finset.univ.image growth, (entry ordered z : ℝ)) -
        (∑ j : Fin stages.length, ∑ i : Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z ∈ (rowCells r)) (j,i) * mean (Sum.inr j))| ≤ V)
    {bits : ℕ} (ε : ℝ)
    (hcompletion :
      let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
      |(rowSum completed r : ℝ) - ((∑ z ∈ rowCells r ∩ full, (entry ordered z : ℝ)) +
        ((rowCells r \ full).card : ℝ) * centralEntriesMean (actualUnusedPool ordered full) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) :
    |(rowSum reference r : ℝ) - (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| <
      ((9 : ℝ) / 2 + B + W + U + V +
        (257 / 250 : ℝ) * poolMaximum n + (19033 / 450 : ℝ) * (201 / 10000 : ℝ) * poolMaximum n) +
        ((1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) := by
  classical
  obtain ⟨_, _, _, _, hbridgec, hwidec, hseedgapc, hgapc, hBscore, hWscore⟩ :=
    fw_completion_family_invariants hP hrect hseedrect hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
      source ordered completed hfixed πb sb πw sw hbridge hwideEntry hseedgap
      (fun j => (stages.get j).gap) hpairgap
  have hcomponents := fw_completion_seed_growth_components hP hrect hseedrect hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols ordered completed hfixed
  dsimp only at hcomponents
  have hBc := hB
  have hWc := hW
  rw [← hBscore (fun z => z ∈ rowCells r)] at hBc
  rw [← hWscore (fun z => z ∈ rowCells r)] at hWc
  have hseedc := hseed
  have hgrowthc := hgrowth
  dsimp only at hseedc hgrowthc
  rw [← hcomponents.2.1 (rowCells r)] at hseedc
  rw [← hcomponents.2.2 (rowCells r)] at hgrowthc
  obtain ⟨_, _, hr, hc, hrow, _⟩ :=
    fw_given_reference_completion_transport hP hrect hseedrect hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
      ordered oldReference completed reference vr vc networkR networkC hslotr hslotc roles hroles
      hfixed hoffactive himage hdactive hdoff hmain hanti hinvrow hinvcol
  let vr' := rowNetworkPairsRebase vr completed hr
  let vc' := rowNetworkPairsRebase vc (LayerPacking.transposePlacement completed) hc
  let nr' := centeredNetworkRebase vr networkR completed hr
  have hslotr' : ∀ t side, rowNetworkSlot vr' (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side := by
    simpa [vr', rowNetworkPairsRebase, rowNetworkSlot] using hslotr
  have hslotc' : ∀ t side, rowNetworkSlot vc' (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side := by
    simpa [vc', rowNetworkPairsRebase, rowNetworkSlot] using hslotc
  have hblockr' : ∀ edge, nr'.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2)) := by
    simpa [nr', centeredNetworkRebase] using hblockr
  have hinvoice : |2 * (rowSum reference r : ℝ) - (physicalNetworkMidpointTwice vr' nr' r : ℝ)| ≤ 9 := by
    exact_mod_cast hrow r
  have hcomparison := fw_first_band_row_residual_bound bmor lower upper hnlo hnhi hP
    hrect hseedrect hwide hoff hs choice br bc sr sc wr wc gr gc
    hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols source completed
    initial batches hvalid blocks hlen hdiag hord hplaced hmatched πb sb πw sw
    hbridgec hwidec hgapc hseedgapc vr' vc' nr' networkC.block
    hslotr' hslotc' hblockr' hblockc reference r hinvoice B W U V hBc hWc hseedc hgrowthc
  exact completion_row_residual_closure ordered completed reference _ r ε _ _ hfixed hcompletion hcomparison

end
end Sude
