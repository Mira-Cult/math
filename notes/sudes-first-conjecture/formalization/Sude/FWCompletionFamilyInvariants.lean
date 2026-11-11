import Sude.FWCompletionFamilyFixed
import Sude.FWGrowthEarlyRolePreservation

/-! Transport the same physical FW family equations and centered scores
through a supplied completion fixing the full geometric reservation. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

/-- The completed square preserves each original family endpoint, the supplied
source-to-ordered block allocation, seed/growth signed gaps and both centered
scores. The source square and each original stage remain fixed. -/
theorem fw_completion_family_invariants {n P : ℕ} (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n) (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (source a c : Cell n ≃ Fin (n*n))
    (hfixed : ∀ z ∈ packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc)), entry c z = entry a z)
    (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8)))) (sb : Fin 5 → Fin (3 * (n + 8)) → Bool)
    (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (sw : Fin (3 * (n / 450)) → Fin (3 * (n + 8)) → Bool)
    (hbridge : ∀ j b p side, entry a (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,b,p),side)) =
      entry source (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,πb j b,doubleBlockPairSwap (sb j b) p),side)))
    (hwideEntry : ∀ j b p side, entry a (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),side)) =
      entry source (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,πw j b,doubleBlockPairSwap (sw j b) p),side)))
    (hseedgap : ∀ j i, entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true)) =
      entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) + 2)
    (gap : Fin P → ℕ)
    (hgap : ∀ j i, entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc ((j,i),true)) =
      entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc ((j,i),false)) + gap j) :
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc
    (∀ x, entry c (bridge x) = entry a (bridge x)) ∧
    (∀ x, entry c (seed x) = entry a (seed x)) ∧
    (∀ x, entry c (wide x) = entry a (wide x)) ∧
    (∀ x, entry c (growth x) = entry a (growth x)) ∧
    (∀ j b p side, entry c (bridge ((j,b,p),side)) =
      entry source (bridge ((j,πb j b,doubleBlockPairSwap (sb j b) p),side))) ∧
    (∀ j b p side, entry c (wide ((j,b,p),side)) =
      entry source (wide ((j,πw j b,doubleBlockPairSwap (sw j b) p),side))) ∧
    (∀ j i, entry c (seed ((j,i),true)) = entry c (seed ((j,i),false)) + 2) ∧
    (∀ j i, entry c (growth ((j,i),true)) = entry c (growth ((j,i),false)) + gap j) ∧
    (∀ line, doubleBlockActualCenteredScore bridge line source c = doubleBlockActualCenteredScore bridge line source a) ∧
    (∀ line, doubleBlockActualCenteredScore wide line source c = doubleBlockActualCenteredScore wide line source a) := by
  classical
  dsimp only
  have hf := fw_completion_family_fixed hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols a c hfixed
  dsimp only at hf
  obtain ⟨_, hb, hs', hw, hg⟩ := hf
  refine ⟨hb, hs', hw, hg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j b p side
    exact (hb _).trans (hbridge j b p side)
  · intro j b p side
    exact (hw _).trans (hwideEntry j b p side)
  · intro j i
    rw [hs' ((j,i),true), hs' ((j,i),false)]
    exact hseedgap j i
  · intro j i
    rw [hg ((j,i),true), hg ((j,i),false)]
    exact hgap j i
  · intro line
    exact double_block_actual_score_preserved _ line source a c hb
  · intro line
    exact double_block_actual_score_preserved _ line source a c hw

end
end Sude
