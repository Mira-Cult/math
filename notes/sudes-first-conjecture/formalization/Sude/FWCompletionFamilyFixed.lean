import Sude.FWFourFamilyPairInjection
import Sude.FWRoleSupportForNetworks
import Sude.FWPhysicalDoubleBlockCells

/-! A supplied completion fixing the full FW reservation fixes every actual
bridge, seed, wide, and growth endpoint, including grouped block indices.
No completion or later-flow existence is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

/-- All four actual family maps lie in the full geometric reservation; hence a
completion that fixes the reservation fixes every family endpoint on the same
ordered and completed squares. -/
theorem fw_completion_family_fixed {n P : ℕ} (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (a c : Cell n ≃ Fin (n*n))
    (hfixed : ∀ z ∈ packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc)), entry c z = entry a z) :
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
    (∀ x, entry c (cells x) = entry a (cells x)) ∧
    (∀ x, entry c (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x) =
      entry a (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x)) ∧
    (∀ x, entry c (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x) =
      entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x)) ∧
    (∀ x, entry c (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x) =
      entry a (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x)) ∧
    (∀ x, entry c (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc x) =
      entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc x)) := by
  classical
  dsimp only
  have hp := fw_four_family_pair_cells_injective hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  have hg := fw_role_support_for_trace_networks hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  dsimp only at hp hg
  have hf (x : FWFourFamilyPairInputs n P) :
      entry c (fwFourFamilyPairCells hrect hseed hwide hoff hs choice
        br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc x) =
      entry a (fwFourFamilyPairCells hrect hseed hwide hoff hs choice
        br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc x) := by
    apply hfixed
    apply hg.2.2.1
    rw [← hp.2]
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  refine ⟨hf, ?_, ?_, ?_, ?_⟩
  · intro x
    exact hf (Sum.inl (Sum.inl (Sum.inl (fwBlockPairIndex 5 n x))))
  · intro x
    exact hf (Sum.inl (Sum.inl (Sum.inr x)))
  · intro x
    exact hf (Sum.inl (Sum.inr (fwBlockPairIndex (3 * (n / 450)) n x)))
  · intro x
    exact hf (Sum.inr x)

end
end Sude
