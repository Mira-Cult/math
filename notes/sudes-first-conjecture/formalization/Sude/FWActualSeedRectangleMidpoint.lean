import Sude.FWActualSeedMidpointCancellation
import Sude.FWSeedRectangleOrientation
import Sude.FWSeedNetworkCoverage

/-! Actual offset seed midpoint bookkeeping. The matched seed ordinary
orientation cancels, perpendicular ordinary orientations vanish, and seed
rectangle orientations and all nonseed terms remain explicit. -/
namespace Sude
noncomputable section
open scoped BigOperators
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- On one row, exact physical support coverage and the midpoint identity
leave the seed rectangle orientation, the original nonseed cells, and the
nonseed network corrections explicitly visible. This concerns the same
pre-centering square and gives no mean or centered-square bound. -/
theorem fw_actual_seed_row_rectangle_midpoint {n L P : ℕ}
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
    let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
    A ∩ ((U.product (Finset.univ : Finset Bool)).image (rowNetworkSlot v)) =
      ((T.product (Finset.univ : Finset Bool)).image (rowNetworkSlot v)) ∧
    (physicalNetworkMidpointTwice v B r : ℝ) =
      2 * (stageLineCentered (fun _ _ => Finset.univ) weights values r ω +
        (∑ j, ((∑ q, weights r j q) * ((∑ q, values j q) / ((6 * (n + 8) : ℕ) : ℝ)))) +
        (gap / 2) * ∑ j : Fin 16, ∑ x : Fin (4 * 6) × Fin 2,
          physicalPairLineOrientation cells (fun c => c.1 = r) (j, prefixDiagonalPairIndex hdiag x)) +
      2 * (∑ c ∈ R \ A, (entry a c : ℝ)) +
      ∑ t ∈ U \ T, (rowNetworkDelta v t r : ℝ) := by
  classical
  dsimp only
  constructor
  · exact fw_seed_centered_row_endpoint_overlap hseed hs choice rect br bc sr sc wr wc gr gc
      hbr hsr hsc hwr hgr hrect hrows hcols v B hslot hblock
  · have hp := fw_actual_seed_row_midpoint_cancellation hseed hs choice br sr wr gr sc
      hbr hsr hwr hgr hsc v B hslot hblock hcells weights values ω gap hweight hmid hgap r
    have ho := fw_seed_row_remaining_orientation hseed hs choice br sr wr gr sc hsr hsc r gap
    dsimp only at hp ho
    linarith

/-- Conditional exact column-network overlap and midpoint decomposition on the
original pre-centering square. The seed rectangles remain explicit. -/
theorem fw_actual_seed_column_rectangle_midpoint {n L P : ℕ}
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
    let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
    ((Finset.univ.image orig) ∩ ((U.product (Finset.univ : Finset Bool)).image
      (fun x => (rowNetworkSlot v x).swap)) =
      ((T.product (Finset.univ : Finset Bool)).image (fun x => (rowNetworkSlot v x).swap))) ∧
    (physicalNetworkMidpointTwice v B c : ℝ) =
      2 * (stageLineCentered (fun _ _ => Finset.univ) weights values c ω +
        (∑ j, ((∑ q, weights c j q) * ((∑ q, values j q) / ((6 * (n + 8) : ℕ) : ℝ)))) +
        (gap / 2) * ∑ j : Fin 16, ∑ rect' : Fin (4 * 6), ∑ pair : Fin 2,
          physicalPairLineOrientation orig (fun x => x.2 = c)
            (j, prefixDiagonalPairIndex hdiag (rect',pair))) +
      2 * (∑ x ∈ R \ A, (entry (LayerPacking.transposePlacement a) x : ℝ)) +
      ∑ t ∈ U \ T, (rowNetworkDelta v t c : ℝ) := by
  classical
  dsimp only
  constructor
  · exact fw_seed_centered_column_endpoint_overlap hseed hs choice rect br bc sr sc wr wc gr gc
      hbc hsr hsc hwc hgc hrect hcols v B hslot hblock
  · have hm := fw_actual_seed_column_midpoint_cancellation hseed hs choice sr bc sc wc gc
      hbc hsr hsc hwc hgc v B hslot hblock hcells weights values ω gap hweight hmid hgap c
    dsimp only at hm
    have ho (p : Fin 16 × Fin (6 * (n + 8))) :
        physicalPairLineOrientation
          (fun x => (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x).swap)
          (fun x => x.1 = c) p =
        physicalPairLineOrientation (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
          (fun x => x.2 = c) p := by
      simp [physicalPairLineOrientation]
    simp_rw [ho] at hm
    have hrem := fw_seed_column_remaining_orientation hseed hs choice sr bc sc wc gc hsr hsc c gap
    dsimp only at hrem
    linarith

end
end Sude
