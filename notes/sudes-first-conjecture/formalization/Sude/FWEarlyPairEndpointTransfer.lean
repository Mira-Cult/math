import Sude.MarkedPairEndpointTransfer
import Sude.FWSeedPairMidpointTransfer
import Sude.FWBridgePairMidpointTransfer
import Sude.FWWidePairMidpointTransfer

/-! Endpoint-set preservation for the actual seed, bridge and wide physical
pairs on two supplied squares. This does not establish a reference switch or
transfer any property to a later flow output. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Every retained seed pair is unchanged or reversed on the supplied
reference, under the explicit rectangle and network pair hypotheses. -/
theorem fw_seed_pair_endpoints_transfer {n L : ℕ}
    (hseed : 5*(4*6) + 16*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16*3) (hsc : sc.length = 16*3)
    (a b : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ packedRectangleSupport hs choice, entry b c = entry a c)
    (hrow : ∀ k, pairEndpointSameOrSwapped a b
      (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k false)
      (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k true))
    (hcol : ∀ k, pairEndpointSameOrSwapped a b
      ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k false).swap)
      ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k true).swap)) :
    let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    ∀ j i, pairEndpointSameOrSwapped a b (cells ((j,i),false)) (cells ((j,i),true)) := by
  classical
  dsimp only
  let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  have hc : ∀ z : Fin 16 × Fin (6*(n+8)),
      (∀ side, cells (z,side) ∈ packedRectangleSupport hs choice) ∨
      (∃ k : Fin ((((br ++ sr) ++ wr) ++ gr).length) × Fin n, ∀ side,
        cells (z,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) k side) ∨
      (∃ k : Fin ((((bc ++ sc) ++ wc) ++ gc).length) × Fin n, ∀ side,
        cells (z,side) = (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k side).swap) := by
    rintro ⟨j,i⟩
    exact fw_seed_pair_network_coverage hseed hs choice br sr wr gr bc sc wc gc hsr hsc j i
  have hm := marked_pair_endpoints_preserved a b (packedRectangleSupport hs choice) cells
    (fun z => layerPairSlot (((br ++ sr) ++ wr) ++ gr) z.1 z.2)
    (fun z => (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) z.1 z.2).swap)
    hfixed hrow hcol hc
  exact fun j i => hm (j,i)

/-- Every actual grouped bridge pair is unchanged or reversed on the same
reference, without requiring a common gap between blocks. -/
theorem fw_bridge_pair_endpoints_transfer {n L : ℕ}
    (hrect : 5*(4*6) ≤ L) (hs : 2*L+1 ≤ n) (choice : Fin L → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5*3) (hbc : bc.length = 5*3)
    (a b : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ packedRectangleSupport hs choice, entry b c = entry a c)
    (hrow : ∀ k, pairEndpointSameOrSwapped a b
      (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k false)
      (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k true))
    (hcol : ∀ k, pairEndpointSameOrSwapped a b
      ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k false).swap)
      ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k true).swap)) :
    let cells := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    ∀ j k p, pairEndpointSameOrSwapped a b (cells ((j,k,p),false)) (cells ((j,k,p),true)) := by
  classical
  dsimp only
  let cells := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
  have hc : ∀ z : Fin 5 × Fin (3*(n+8)) × Fin 2,
      (∀ side, cells (z,side) ∈ packedRectangleSupport hs choice) ∨
      (∃ k : Fin ((((br ++ sr) ++ wr) ++ gr).length) × Fin n, ∀ side,
        cells (z,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) k side) ∨
      (∃ k : Fin ((((bc ++ sc) ++ wc) ++ gc).length) × Fin n, ∀ side,
        cells (z,side) = (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k side).swap) := by
    rintro ⟨j,k,p⟩
    exact fw_bridge_pair_network_coverage hrect hs choice br sr wr gr bc sc wc gc hbr hbc j k p
  have hm := marked_pair_endpoints_preserved a b (packedRectangleSupport hs choice) cells
    (fun z => layerPairSlot (((br ++ sr) ++ wr) ++ gr) z.1 z.2)
    (fun z => (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) z.1 z.2).swap)
    hfixed hrow hcol hc
  exact fun j k p => hm (j,k,p)

/-- Every actual grouped wide pair is unchanged or reversed on the same
reference, allowing a different gap for every block. -/
theorem fw_wide_pair_endpoints_transfer {n L : ℕ}
    (hwide : 5*(4*6) + 16*(4*6) + (3*(n/450))*(4*6) ≤ L)
    (hs : 2*L+1 ≤ n) (choice : Fin L → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3*(n/450))*3) (hwc : wc.length = (3*(n/450))*3)
    (a b : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ packedRectangleSupport hs choice, entry b c = entry a c)
    (hrow : ∀ k, pairEndpointSameOrSwapped a b
      (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k false)
      (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k true))
    (hcol : ∀ k, pairEndpointSameOrSwapped a b
      ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k false).swap)
      ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k true).swap)) :
    let cells := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    ∀ j k p, pairEndpointSameOrSwapped a b (cells ((j,k,p),false)) (cells ((j,k,p),true)) := by
  classical
  dsimp only
  let cells := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
  have hc : ∀ z : Fin (3*(n/450)) × Fin (3*(n+8)) × Fin 2,
      (∀ side, cells (z,side) ∈ packedRectangleSupport hs choice) ∨
      (∃ k : Fin ((((br ++ sr) ++ wr) ++ gr).length) × Fin n, ∀ side,
        cells (z,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) k side) ∨
      (∃ k : Fin ((((bc ++ sc) ++ wc) ++ gc).length) × Fin n, ∀ side,
        cells (z,side) = (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k side).swap) := by
    rintro ⟨j,k,p⟩
    exact fw_wide_pair_network_coverage hwide hs choice br sr wr gr bc sc wc gc hwr hwc j k p
  have hm := marked_pair_endpoints_preserved a b (packedRectangleSupport hs choice) cells
    (fun z => layerPairSlot (((br ++ sr) ++ wr) ++ gr) z.1 z.2)
    (fun z => (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) z.1 z.2).swap)
    hfixed hrow hcol hc
  exact fun j k p => hm (j,k,p)

end
end Sude
