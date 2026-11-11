import Sude.FWActualSeedRectangleMidpoint
import Sude.FWSeedRectangleOrientationZero

/-! Row and column midpoint bookkeeping after exact seed-rectangle orientation
cancellation. No diagonal or complete-line bound is asserted. -/
namespace Sude
noncomputable section
open scoped BigOperators
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- Exact row support and midpoint identity with no seed rectangle orientation. -/
theorem fw_actual_seed_row_midpoint_no_rectangle_orientation {n L P : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rect : Finset (Cell n))
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (hrect : packedRectangleSupport hs choice ⊆ rect)
    (hrows : LayerPacking.PackedLayers rect (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
    {a : Cell n ≃ Fin (n*n)}
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
    A ∩ ((U.product (Finset.univ : Finset Bool)).image (rowNetworkSlot v)) =
      ((T.product (Finset.univ : Finset Bool)).image (rowNetworkSlot v)) ∧
    (physicalNetworkMidpointTwice v B r : ℝ) =
      2 * (stageLineCentered (fun _ _ => Finset.univ) weights values r ω +
        (∑ j, ((∑ q, weights r j q) * ((∑ q, values j q) / ((6 * (n + 8) : ℕ) : ℝ))))) +
      2 * (∑ c ∈ R \ A, (entry a c : ℝ)) +
      ∑ t ∈ U \ T, (rowNetworkDelta v t r : ℝ) := by
  have hp := fw_actual_seed_row_rectangle_midpoint hseed hs choice rect br bc sr sc wr wc gr gc
    hbr hsr hsc hwr hgr hrect hrows hcols v B hslot hblock hcells weights values ω gap hweight hmid hgap r
  dsimp only at hp ⊢
  rw [fw_seed_rectangle_row_orientation_sum_zero hseed hs choice sr sc hsr hsc r] at hp
  simpa using hp

/-- The transposed-column counterpart. -/
theorem fw_actual_seed_column_midpoint_no_rectangle_orientation {n L P : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rect : Finset (Cell n))
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbc : bc.length = 5 * 3) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (hgc : gc.length = P * 3)
    (hrect : packedRectangleSupport hs choice ⊆ rect)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
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
    let orig := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let cells := fun x => (orig x).swap
    let A := Finset.univ.image cells
    let R := (Finset.univ : Finset (Fin n)).image (fun r => (c,r))
    let U := Finset.univ.biUnion B.block
    let T := fwSeedJointPairImage bc sc wc gc hsc
    ((Finset.univ.image orig) ∩ ((U.product (Finset.univ : Finset Bool)).image
      (fun x => (rowNetworkSlot v x).swap)) =
      ((T.product (Finset.univ : Finset Bool)).image (fun x => (rowNetworkSlot v x).swap))) ∧
    (physicalNetworkMidpointTwice v B c : ℝ) =
      2 * (stageLineCentered (fun _ _ => Finset.univ) weights values c ω +
        (∑ j, ((∑ q, weights c j q) * ((∑ q, values j q) / ((6 * (n + 8) : ℕ) : ℝ))))) +
      2 * (∑ x ∈ R \ A, (entry (LayerPacking.transposePlacement a) x : ℝ)) +
      ∑ t ∈ U \ T, (rowNetworkDelta v t c : ℝ) := by
  have hp := fw_actual_seed_column_rectangle_midpoint hseed hs choice rect br bc sr sc wr wc gr gc
    hbc hsr hsc hwc hgc hrect hcols v B hslot hblock hcells weights values ω gap hweight hmid hgap c
  dsimp only at hp ⊢
  rw [fw_seed_rectangle_column_orientation_sum_zero hseed hs choice sr sc hsr hsc c] at hp
  simpa using hp

end
end Sude
