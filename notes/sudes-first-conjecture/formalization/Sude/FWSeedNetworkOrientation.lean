import Sude.FWSeedNetworkMatching
import Sude.FWSeedMidpointPartition

/-! Specialize the matched-pair orientation cancellation to the actual
offset seed row and column network slots. No concentration is transferred
to a centered square. -/
namespace Sude
noncomputable section
open scoped BigOperators
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- Every actual seed-band row correction equals the negative orientation
contribution of its corresponding selected seed pair. -/
theorem fw_seed_joint_row_orientation_sum {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (br sr wr gr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) a)
    (hslot : ∀ t side, rowNetworkSlot v (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (gap : ℝ) (hgap : ∀ j q,
      (entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),true)) : ℝ) -
        entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),false)) = gap)
    (r : Fin n) :
    (∑ t ∈ fwSeedJointPairImage br sr wr gr hsr, (rowNetworkDelta v t r : ℝ)) =
      -gap * ∑ t ∈ fwSeedJointPairImage br sr wr gr hsr,
        physicalPairLineOrientation (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
          (fun c => c.1 = r) (fwSeedJointToOrdinaryIndex br sr wr gr hsr 0 t) := by
  classical
  apply physical_network_matched_delta_sum v (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
    (fwSeedJointPairImage br sr wr gr hsr) (fwSeedJointToOrdinaryIndex br sr wr gr hsr 0) r gap
  · exact fw_seed_joint_row_side_matching hseed hs choice br sr wr gr sc hsr hsc v hslot
  · intro t ht
    exact hgap (fwSeedJointToOrdinaryIndex br sr wr gr hsr 0 t).1
      (fwSeedJointToOrdinaryIndex br sr wr gr hsr 0 t).2

/-- The same cancellation for the column network, in transposed-square
coordinates. -/
theorem fw_seed_joint_column_orientation_sum {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr bc sc wc gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n)
      (LayerPacking.transposePlacement a))
    (hslot : ∀ t side, rowNetworkSlot v (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side)
    (gap : ℝ) (hgap : ∀ j q,
      (entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),true)) : ℝ) -
        entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),false)) = gap)
    (c : Fin n) :
    (∑ t ∈ fwSeedJointPairImage bc sc wc gc hsc, (rowNetworkDelta v t c : ℝ)) =
      -gap * ∑ t ∈ fwSeedJointPairImage bc sc wc gc hsc,
        physicalPairLineOrientation (fun x => (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x).swap)
          (fun x => x.1 = c) (fwSeedJointToOrdinaryIndex bc sc wc gc hsc 1 t) := by
  classical
  apply physical_network_matched_delta_sum v
    (fun x => (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x).swap)
    (fwSeedJointPairImage bc sc wc gc hsc) (fwSeedJointToOrdinaryIndex bc sc wc gc hsc 1) c gap
  · exact fw_seed_joint_column_side_matching hseed hs choice sr bc sc wc gc hsr hsc v hslot
  · intro t ht
    simpa [LayerPacking.transposePlacement, entry] using
      hgap (fwSeedJointToOrdinaryIndex bc sc wc gc hsc 1 t).1
        (fwSeedJointToOrdinaryIndex bc sc wc gc hsc 1 t).2

end
end Sude
