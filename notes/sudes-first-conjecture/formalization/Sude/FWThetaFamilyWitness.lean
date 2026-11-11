import Sude.FWGivenThetaDQRFAllLineFlows
import Sude.FWThetaSeedGrowthLineBounds

/-! A focused carrier for the four-family geometry and the original score and
placement inputs of the first-band assembly. All fields refer to the same
ordered square. In particular the bridge initial set is empty; `initial` is
only the unrelated initial pool of the growth trace. This record asserts no
completion, numerical gate, or later-flow conclusion. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

structure FWThetaFamilyWitness (n L : ℕ) (choice : Fin L → Bool) where
  stages : List BTSelectedStage
  stageCap : stages.length ≤ 238
  hrect : 5 * (4*6) ≤ L
  hseedrect : 5*(4*6) + 16*(4*6) ≤ L
  hwide : 5*(4*6) + 16*(4*6) + (3*(n/450))*(4*6) ≤ L
  hoff : 5*(4*6) + 16*(4*6) + (3*(n/450))*(4*6) + stages.length*(4*6) ≤ L
  hs : 2*L+1 ≤ n
  br : List (LayerPacking.Layer n)
  bc : List (LayerPacking.Layer n)
  sr : List (LayerPacking.Layer n)
  sc : List (LayerPacking.Layer n)
  wr : List (LayerPacking.Layer n)
  wc : List (LayerPacking.Layer n)
  gr : List (LayerPacking.Layer n)
  gc : List (LayerPacking.Layer n)
  hbr : br.length = 5*3
  hbc : bc.length = 5*3
  hsr : sr.length = 16*3
  hsc : sc.length = 16*3
  hwr : wr.length = (3*(n/450))*3
  hwc : wc.length = (3*(n/450))*3
  hgr : gr.length = stages.length*3
  hgc : gc.length = stages.length*3
  hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr)
  hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
    (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
    (((bc ++ sc) ++ wc) ++ gc)
  source : Cell n ≃ Fin (n*n)
  grown : Cell n ≃ Fin (n*n)
  ordered : Cell n ≃ Fin (n*n)
  batches : ℕ → List DoublePair
  hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j
  blocks : List DoublePair
  hlen : blocks.length = (3*(n/450))*(3*(n+8))
  hdiag : ∀ t side, entry source (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
    fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeDiagonalSlot n (t,side))
  hord : ∀ x, entry source (fwBridgeLayerCells br bc hbr hbc x) =
    fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x)
  hplaced : ∀ x : FWWideInputs n, entry source (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
    doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2)
  hmatched : ∀ block ∈ blocks, block.MatchedValid
    (bmorLowBins (fwReflectedLeft ((Lucas.poolTotal n : ℝ) / (n*n : ℕ)) (poolMaximum n))
      (fwReflectedRight ((Lucas.poolTotal n : ℝ) / (n*n : ℕ)) (poolMaximum n)))
    (bmorHighBins (fwReflectedLeft ((Lucas.poolTotal n : ℝ) / (n*n : ℕ)) (poolMaximum n))
      (fwReflectedRight ((Lucas.poolTotal n : ℝ) / (n*n : ℕ)) (poolMaximum n)))
  πb : Fin 5 → Equiv.Perm (Fin (3*(n+8)))
  sb : Fin 5 → Fin (3*(n+8)) → Bool
  πw : Fin (3*(n/450)) → Equiv.Perm (Fin (3*(n+8)))
  sw : Fin (3*(n/450)) → Fin (3*(n+8)) → Bool
  hbridge : ∀ j k p side,
    entry ordered (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,k,p),side)) =
      entry source (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
        ((j,πb j k,doubleBlockPairSwap (sb j k) p),side))
  hwideEntry : ∀ j k p side,
    entry ordered (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,k,p),side)) =
      entry source (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
        ((j,πw j k,doubleBlockPairSwap (sw j k) p),side))
  gapb : Fin 5 → Fin (3*(n+8)) → ℕ
  gapw : Fin (3*(n/450)) → Fin (3*(n+8)) → ℕ
  hinvoiceb : ∀ j k p,
    entry ordered (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,k,p),true)) =
      entry ordered (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,k,p),false)) + gapb j k
  hinvoicew : ∀ j k p,
    entry ordered (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,k,p),true)) =
      entry ordered (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,k,p),false)) + gapw j k
  hpairgap : ∀ j i, entry ordered (btGrowingOffsetPairCells (Q := 6*(n+8))
    (by omega) (by omega) (by omega) (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc ((j,i),true)) =
      entry ordered (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc ((j,i),false)) + (stages.get j).gap
  hseedgap : ∀ j q, entry ordered (fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc ((j,q),true)) =
    entry ordered (fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc ((j,q),false)) + 2
  hBridgeScore : ∀ l : Fin ((n+n)+2),
    |doubleBlockActualCenteredScore (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
      (fun z => z ∈ physicalAllLineCells l) source ordered| <
      (poolMaximum n : ℝ) * (23/924 : ℝ) * Real.sqrt (94*Real.log (8*(n : ℝ)+8))
  hWideScore : ∀ l : Fin ((n+n)+2),
    |doubleBlockActualCenteredScore (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
      (fun z => z ∈ physicalAllLineCells l) source ordered| <
      (poolMaximum n : ℝ) * (2/235 : ℝ) * Real.sqrt ((54*((n/450 : ℕ) : ℝ)+4)*Real.log (8*(n : ℝ)+8))
  initial : Finset ℕ
  stock : Finset ℕ
  last : ℕ
  trace : BTGrowingTrace 2 (6*(n+8)) initial 32 stock last stages
  hpool : ∀ p ∈ initial, p ∈ pool n
  ωseed : Fin 16 → Equiv.Perm (Fin (6*(n+8)))
  τ : Fin stages.length → Equiv.Perm (Fin (6*(n+8)))
  hseedPlace : ∀ j i side,
    entry ordered (fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc ((j,i),side)) =
      entry grown (fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc ((j,ωseed j i),side))
  hgrowthPlace : ∀ x,
    entry ordered (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc x) =
      (trace.poolValues rfl hpool (stagePairPermutation τ x)).val
  hseedScore : ∀ l : Fin ((n+n)+2),
    let seed := fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc
    let line := fun z => z ∈ physicalAllLineCells l
    let value := fun j i => (((entry grown (seed ((j,i),false)) : ℝ) + entry grown (seed ((j,i),true))) / 2)
    |(∑ z ∈ (Finset.univ.image seed).filter line, (entry ordered z : ℝ)) -
      (∑ j, ((∑ i, physicalPairLineWeight seed line (j,i)) *
        ((∑ i, value j i) / ((6*(n+8) : ℕ) : ℝ)))) -
      (∑ p, physicalPairLineOrientation seed line p * ((2 : ℝ)/2))| ≤
      Real.sqrt (((11/2 : ℝ)*((2^30 : ℕ) : ℝ)^2)*Real.log (4 * (((n+n)+2 : ℕ) : ℝ))/2)
  hgrowthRow : ∀ r : Fin n,
    let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc
    let mean := fun j : Fin stages.length =>
      (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) / ((6*(n+8) : ℕ) : ℝ)
    |∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z.1 = r) p *
      ((((entry ordered (growth (p,true)) : ℝ) + entry ordered (growth (p,false))) / 2) - mean p.1)| ≤
      (Nat.clog 2 (6*n) : ℝ)*(8*((poolMaximum n : ℝ)/6)) +
        3*((poolMaximum n : ℝ)/6)/(n : ℝ) + 2*((poolMaximum n : ℝ)/6)
  hgrowthCol : ∀ c : Fin n,
    let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc
    let mean := fun j : Fin stages.length =>
      (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) / ((6*(n+8) : ℕ) : ℝ)
    |∑ p : Fin stages.length × Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z.2 = c) p *
      ((((entry ordered (growth (p,true)) : ℝ) + entry ordered (growth (p,false))) / 2) - mean p.1)| ≤
      (Nat.clog 2 (6*n) : ℝ)*(8*((poolMaximum n : ℝ)/6)) +
        3*((poolMaximum n : ℝ)/6)/(n : ℝ) + 2*((poolMaximum n : ℝ)/6)

end
end Sude
