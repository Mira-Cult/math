import Sude.FWBridgeWideNetworkMatching
import Sude.DoubleBlockPhysicalMidpointPartition

/-! Exact bridge-family contribution to a physical row midpoint. The
unmatched orientations, non-bridge cells, and other network deltas remain. -/
namespace Sude
noncomputable section

/-- Instantiate the one-family partition with the actual bridge band of the
joint row network. The grouped cells, decoder, supported blocks, and side
matches all refer to the same supplied geometry and new square. -/
theorem fw_bridge_row_midpoint_partition {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br sr wr gr bc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3)
    (hcells : Function.Injective (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc))
    (old new : Cell n ≃ Fin (n*n))
    (v : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) new)
    (network : CenteredNetwork (Fin 3 × Fin n)
      (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) v)
    (hslot : ∀ t side, rowNetworkSlot v (t,side) =
      layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (hblock : ∀ edge, network.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2)))
    (r : Fin n) :
    let cells := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let T := fwBridgeJointPairImage br sr wr gr hbr
    let ι := fwBridgeJointToGrouped br sr wr gr hbr 0
    let A := Finset.univ.image cells
    let row := (Finset.univ : Finset (Fin n)).image (fun c => (r,c))
    let U := Finset.univ.biUnion network.block
    let line := fun c : Cell n => c.1 = r
    let gap := fun i => (entry new (cells (i,true)) : ℝ) - entry new (cells (i,false))
    (physicalNetworkMidpointTwice v network r : ℝ) =
      2 * doubleBlockActualCenteredScore cells line old new +
      2 * (∑ j, ∑ b, doubleBlockLineWeight cells line j b * doubleStageMidpointMean cells old j) +
      (∑ i ∈ Finset.univ \ T.image ι, gap i * physicalPairLineOrientation cells line i) +
      2 * (∑ c ∈ row \ A, (entry new c : ℝ)) +
      ∑ k ∈ U \ T, (rowNetworkDelta v k r : ℝ) := by
  classical
  exact double_block_physical_midpoint_partition
    (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc) hcells old new v network
    (fwBridgeJointPairImage br sr wr gr hbr)
    (fw_bridge_joint_image_subset_blocks br sr wr gr hbr hsr hwr hgr network.block hblock)
    (fwBridgeJointToGrouped br sr wr gr hbr 0)
    (fw_bridge_joint_grouped_injective_on_image br sr wr gr hbr 0) r
    (fw_bridge_joint_row_side_matching hrect hs choice br sr wr gr bc hbr hbc v hslot)

end
end Sude
