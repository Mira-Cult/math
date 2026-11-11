import Sude.FWSeedNetworkMatching
import Sude.FWSeedMidpointCancellation

/-! Actual offset seed-network specialization of the generic midpoint
cancellation identity. The complement and all nonseed network corrections
remain explicit, with no centered-reference concentration claim. -/
namespace Sude
noncomputable section
open scoped BigOperators
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- For the actual row-network seed band, the selected seed orientation
contains every selected seed pair, while only matching seed-band network
pairs are cancelled. Other seed roles and every nonseed row contribution and
network correction are retained in the displayed terms. -/
theorem fw_actual_seed_row_midpoint_cancellation {n L P : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (br sr wr gr sc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (hsc : sc.length = 16 * 3) {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) a)
    (B : CenteredNetwork (Fin 3 × Fin n) (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) v)
    (hslot : ∀ t side, rowNetworkSlot v (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (hblock : ∀ edge, B.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2)))
    (hcells : Function.Injective (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc))
    (weights : Fin n → Fin 16 → Fin (6 * (n + 8)) → ℝ)
    (values : Fin 16 → Fin (6 * (n + 8)) → ℝ)
    (ω : Fin 16 → Equiv.Perm (Fin (6 * (n + 8)))) (gap : ℝ)
    (hweight : ∀ r j q, physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
      (fun c => c.1 = r) (j,q) = weights r j q)
    (hmid : ∀ j q, (((entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),false)) : ℝ) +
      entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),true))) / 2) = values j (ω j q))
    (hgap : ∀ j q, (entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),true)) : ℝ) -
      entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),false)) = gap)
    (r : Fin n) :
    let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let A := Finset.univ.image cells
    let R := (Finset.univ : Finset (Fin n)).image (fun c => (r,c))
    let U := Finset.univ.biUnion B.block
    let T := fwSeedJointPairImage br sr wr gr hsr
    let ι := fwSeedJointToOrdinaryIndex br sr wr gr hsr 0
    (physicalNetworkMidpointTwice v B r : ℝ) =
      2 * (stageLineCentered (fun _ _ => Finset.univ) weights values r ω +
        (∑ j, ((∑ q, weights r j q) * ((∑ q, values j q) / ((6 * (n + 8) : ℕ) : ℝ)))) +
        (∑ p, physicalPairLineOrientation cells (fun c => c.1 = r) p * (gap / 2)) -
        (gap / 2) * ∑ t ∈ T, physicalPairLineOrientation cells (fun c => c.1 = r) (ι t)) +
      2 * (∑ c ∈ R \ A, (entry a c : ℝ)) +
      ∑ t ∈ U \ T, (rowNetworkDelta v t r : ℝ) := by
  classical
  dsimp only
  apply physical_network_midpoint_seed_cancellation (by omega) v B
    (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) hcells weights values ω gap hweight hmid hgap
    (fwSeedJointPairImage br sr wr gr hsr)
    (fw_seed_joint_image_subset_blocks br sr wr gr hbr hsr hwr hgr B.block hblock)
    (fwSeedJointToOrdinaryIndex br sr wr gr hsr 0)
  exact fw_seed_joint_row_side_matching hseed hs choice br sr wr gr sc hsr hsc v hslot

/-- The actual column-network counterpart is expressed in transposed
coordinates; its complement therefore includes every original column cell
outside the complete selected seed support. -/
theorem fw_actual_seed_column_midpoint_cancellation {n L P : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr bc sc wc gc : List (LayerPacking.Layer n))
    (hbc : bc.length = 5 * 3) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (hgc : gc.length = P * 3)
    {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n)
      (LayerPacking.transposePlacement a))
    (B : CenteredNetwork (Fin 3 × Fin n) (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) v)
    (hslot : ∀ t side, rowNetworkSlot v (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side)
    (hblock : ∀ edge, B.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex bc sc wc gc hbc hsc hwc hgc ((x,edge.1),edge.2)))
    (hcells : Function.Injective (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc))
    (weights : Fin n → Fin 16 → Fin (6 * (n + 8)) → ℝ)
    (values : Fin 16 → Fin (6 * (n + 8)) → ℝ)
    (ω : Fin 16 → Equiv.Perm (Fin (6 * (n + 8)))) (gap : ℝ)
    (hweight : ∀ c j q, physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
      (fun x => x.2 = c) (j,q) = weights c j q)
    (hmid : ∀ j q, (((entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),false)) : ℝ) +
      entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),true))) / 2) = values j (ω j q))
    (hgap : ∀ j q, (entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),true)) : ℝ) -
      entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),false)) = gap)
    (c : Fin n) :
    let cells := fun x => (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x).swap
    let A := Finset.univ.image cells
    let R := (Finset.univ : Finset (Fin n)).image (fun r => (c,r))
    let U := Finset.univ.biUnion B.block
    let T := fwSeedJointPairImage bc sc wc gc hsc
    let ι := fwSeedJointToOrdinaryIndex bc sc wc gc hsc 1
    (physicalNetworkMidpointTwice v B c : ℝ) =
      2 * (stageLineCentered (fun _ _ => Finset.univ) weights values c ω +
        (∑ j, ((∑ q, weights c j q) * ((∑ q, values j q) / ((6 * (n + 8) : ℕ) : ℝ)))) +
        (∑ p, physicalPairLineOrientation cells (fun x => x.1 = c) p * (gap / 2)) -
        (gap / 2) * ∑ t ∈ T, physicalPairLineOrientation cells (fun x => x.1 = c) (ι t)) +
      2 * (∑ x ∈ R \ A, (entry (LayerPacking.transposePlacement a) x : ℝ)) +
      ∑ t ∈ U \ T, (rowNetworkDelta v t c : ℝ) := by
  classical
  dsimp only
  let cells := fun x => (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x).swap
  have hcells' : Function.Injective cells := by
    intro x y h
    apply hcells
    have hh := congrArg Prod.swap h
    simpa [cells] using hh
  have hweight' : ∀ c j q, physicalPairLineWeight cells (fun x => x.1 = c) (j,q) = weights c j q := by
    intro c j q
    simpa [cells, physicalPairLineWeight] using hweight c j q
  have hmid' : ∀ j q, (((entry (LayerPacking.transposePlacement a) (cells ((j,q),false)) : ℝ) +
      entry (LayerPacking.transposePlacement a) (cells ((j,q),true))) / 2) = values j (ω j q) := by
    intro j q
    simpa [cells, LayerPacking.transposePlacement, entry] using hmid j q
  have hgap' : ∀ j q, (entry (LayerPacking.transposePlacement a) (cells ((j,q),true)) : ℝ) -
      entry (LayerPacking.transposePlacement a) (cells ((j,q),false)) = gap := by
    intro j q
    simpa [cells, LayerPacking.transposePlacement, entry] using hgap j q
  apply physical_network_midpoint_seed_cancellation (by omega) v B cells hcells' weights values ω gap
    hweight' hmid' hgap' (fwSeedJointPairImage bc sc wc gc hsc)
    (fw_seed_joint_image_subset_blocks bc sc wc gc hbc hsc hwc hgc B.block hblock)
    (fwSeedJointToOrdinaryIndex bc sc wc gc hsc 1)
  exact fw_seed_joint_column_side_matching hseed hs choice sr bc sc wc gc hsr hsc v hslot

end
end Sude
