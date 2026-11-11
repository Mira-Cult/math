import Sude.FWReservedMidpointComponentAssembly
import Sude.FWPairGapColumnReferenceMidpoint

/-! Conditional physical column midpoint assembly for one fixed ordered square
and one supplied reference. Spare and free cells remain explicit. No full-line,
numeric gate, diagonal-primality or later-flow conclusion is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

theorem fw_reserved_midpoint_column {n : ℕ} {stages : List BTSelectedStage} (hP : stages.length ≤ 238)
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
    (source ordered : Cell n ≃ Fin (n*n))
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
    (networkC : CenteredNetwork (Fin 3 × Fin n) (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) vc)
    (blocksR : (Fin 3 × Fin n) → Finset (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n))
    (hslotr : ∀ t side, rowNetworkSlot vr (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (hslotc : ∀ t side, rowNetworkSlot vc (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side)
    (hblockr : ∀ edge, blocksR edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2)))
    (hblockc : ∀ edge, networkC.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex bc sc wc gc hbc hsc hwc hgc ((x,edge.1),edge.2)))
    (gapb : Fin 5 → Fin (3 * (n + 8)) → ℕ)
    (gapw : Fin (3 * (n / 450)) → Fin (3 * (n + 8)) → ℕ)
    (hinvoiceb : ∀ j b p,
      entry ordered (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,b,p),true)) =
      entry ordered (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,b,p),false)) + gapb j b)
    (hinvoicew : ∀ j b p,
      entry ordered (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),true)) =
      entry ordered (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),false)) + gapw j b)
    (reference : Cell n ≃ Fin (n*n)) (c : Fin n)
    (hinvoice : |2 * (columnSum reference c : ℤ) - physicalNetworkMidpointTwice vc networkC c| ≤ 9)
    (B W U V : ℝ)
    (hB : |doubleBlockActualCenteredScore (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
      (fun z => z ∈ (columnCells c)) source ordered| ≤ B)
    (hW : |doubleBlockActualCenteredScore (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
      (fun z => z ∈ (columnCells c)) source ordered| ≤ W)
    (hseed :
      let cells := fwFourFamilyPairCells hrect hseedrect hwide hoff hs choice
        br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n stages.length
      let mean := fun j : FWFourStageIndex n stages.length =>
        (∑ i, (((entry ordered (cells ((j,i),false)) : ℝ) + entry ordered (cells ((j,i),true))) / 2)) /
          ((6 * (n + 8) : ℕ) : ℝ)
      let seed := fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc
      |(∑ z ∈ (columnCells c) ∩ Finset.univ.image seed, (entry ordered z : ℝ)) -
        (∑ j : Fin 16, ∑ i : Fin (6*(n+8)), physicalPairLineWeight seed (fun z => z ∈ (columnCells c)) (j,i) *
          mean (Sum.inl (Sum.inl (Sum.inr j))))| ≤ U)
    (hgrowth :
      let cells := fwFourFamilyPairCells hrect hseedrect hwide hoff hs choice
        br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n stages.length
      let mean := fun j : FWFourStageIndex n stages.length =>
        (∑ i, (((entry ordered (cells ((j,i),false)) : ℝ) + entry ordered (cells ((j,i),true))) / 2)) /
          ((6 * (n + 8) : ℕ) : ℝ)
      let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc
      |(∑ z ∈ (columnCells c) ∩ Finset.univ.image growth, (entry ordered z : ℝ)) -
        (∑ j : Fin stages.length, ∑ i : Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z ∈ (columnCells c)) (j,i) * mean (Sum.inr j))| ≤ V) :
    let cells := fwFourFamilyPairCells hrect hseedrect hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n stages.length
    let mean := fun j : FWFourStageIndex n stages.length =>
        (∑ i, (((entry ordered (cells ((j,i),false)) : ℝ) + entry ordered (cells ((j,i),true))) / 2)) /
          ((6 * (n + 8) : ℕ) : ℝ)
    let roles := fwGrowthEarlyRoleCells hrect hseedrect hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    |(columnSum reference c : ℝ) - ((∑ j : FWFourStageIndex n stages.length, ∑ i : Fin (6*(n+8)),
      physicalPairLineWeight cells (fun z => z ∈ (columnCells c)) (j,i) * mean j) +
      (∑ z ∈ (columnCells c) ∩ (full \ roles), (entry ordered z : ℝ)) +
      (∑ z ∈ (columnCells c) \ full, (entry ordered z : ℝ)))| ≤ (9 : ℝ) / 2 + B + W + U + V := by
  classical
  let cells := fwFourFamilyPairCells hrect hseedrect hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n stages.length
  let mean := fun j : FWFourStageIndex n stages.length =>
    (∑ i, (((entry ordered (cells ((j,i),false)) : ℝ) + entry ordered (cells ((j,i),true))) / 2)) /
      ((6 * (n + 8) : ℕ) : ℝ)
  have hcore := fw_pair_gap_column_reference_midpoint_comparison hP hrect hseedrect hwide hoff
    (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols source ordered
    hpairgap hseedgap vr vc networkC hslotr hslotc blocksR hblockr hblockc
    gapb gapw hinvoiceb hinvoicew c reference hinvoice
  have h := fw_reserved_midpoint_component_assembly hP hrect hseedrect hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols source ordered
    πb sb πw sw hbridge hwideEntry (columnCells c) (columnSum reference c : ℝ) (9 / 2 : ℝ) B W U V
    mean (fun _ => rfl) ?_ hB hW hseed hgrowth
  · exact h
  · have hline : (fun z : Cell n => z ∈ columnCells c) = (fun z : Cell n => z.2 = c) := by
      funext z
      exact propext (mem_columnCells c z)
    rw [hline]
    simpa only [columnCells] using hcore

end
end Sude
