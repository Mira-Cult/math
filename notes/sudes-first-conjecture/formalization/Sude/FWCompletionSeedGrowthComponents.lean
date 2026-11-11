import Sude.FWCompletionFamilyFixed
import Sude.FWFourFamilyStageTotals
import Sude.PhysicalPairLineSum

/-! Exact transfer of seed/growth physical component comparisons between
an ordered square and a completion fixing the same full FW reservation.
No component bound, completion existence, final line or flow is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem fw_completion_seed_growth_components {n P : ℕ} (hP : P ≤ 238)
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
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
    let means := fun (square : Cell n ≃ Fin (n*n)) (j : FWFourStageIndex n P) =>
      (∑ i, (((entry square (cells ((j,i),false)) : ℝ) + entry square (cells ((j,i),true))) / 2)) /
        ((6 * (n + 8) : ℕ) : ℝ)
    let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc
    (∀ j, means c j = means a j) ∧
    (∀ line : Finset (Cell n),
      (∑ z ∈ line ∩ Finset.univ.image seed, (entry c z : ℝ)) -
        (∑ j : Fin 16, ∑ i, physicalPairLineWeight seed (fun z => z ∈ line) (j,i) *
          means c (Sum.inl (Sum.inl (Sum.inr j)))) =
      (∑ z ∈ line ∩ Finset.univ.image seed, (entry a z : ℝ)) -
        (∑ j : Fin 16, ∑ i, physicalPairLineWeight seed (fun z => z ∈ line) (j,i) *
          means a (Sum.inl (Sum.inl (Sum.inr j))))) ∧
    (∀ line : Finset (Cell n),
      (∑ z ∈ line ∩ Finset.univ.image growth, (entry c z : ℝ)) -
        (∑ j : Fin P, ∑ i, physicalPairLineWeight growth (fun z => z ∈ line) (j,i) * means c (Sum.inr j)) =
      (∑ z ∈ line ∩ Finset.univ.image growth, (entry a z : ℝ)) -
        (∑ j : Fin P, ∑ i, physicalPairLineWeight growth (fun z => z ∈ line) (j,i) * means a (Sum.inr j))) := by
  classical
  dsimp only
  let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
  let means := fun (square : Cell n ≃ Fin (n*n)) (j : FWFourStageIndex n P) =>
    (∑ i, (((entry square (cells ((j,i),false)) : ℝ) + entry square (cells ((j,i),true))) / 2)) /
      ((6 * (n + 8) : ℕ) : ℝ)
  let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
    (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc
  have hf := fw_completion_family_fixed hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols a c hfixed
  dsimp only at hf
  have hc (j : FWFourStageIndex n P) (i : Fin (6*(n+8))) (side : Bool) :
      entry c (cells ((j,i),side)) = entry a (cells ((j,i),side)) :=
    hf.1 (fwFourStageInputEquiv n P ((j,i),side))
  have hm : ∀ j, means c j = means a j := by
    intro j
    dsimp [means]
    simp only [hc]
  have hseedLine (line : Finset (Cell n)) :
      (∑ z ∈ line ∩ Finset.univ.image seed, (entry c z : ℝ)) =
      ∑ z ∈ line ∩ Finset.univ.image seed, (entry a z : ℝ) := by
    apply Finset.sum_congr rfl
    intro z hz
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hz).2
    rw [← hx, hf.2.2.1]
  have hgrowthLine (line : Finset (Cell n)) :
      (∑ z ∈ line ∩ Finset.univ.image growth, (entry c z : ℝ)) =
      ∑ z ∈ line ∩ Finset.univ.image growth, (entry a z : ℝ) := by
    apply Finset.sum_congr rfl
    intro z hz
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hz).2
    rw [← hx, hf.2.2.2.2]
  refine ⟨hm, ?_, ?_⟩
  · intro line
    change (∑ z ∈ line ∩ Finset.univ.image seed, (entry c z : ℝ)) -
      (∑ j : Fin 16, ∑ i, physicalPairLineWeight seed (fun z => z ∈ line) (j,i) * means c (Sum.inl (Sum.inl (Sum.inr j)))) =
      (∑ z ∈ line ∩ Finset.univ.image seed, (entry a z : ℝ)) -
      (∑ j : Fin 16, ∑ i, physicalPairLineWeight seed (fun z => z ∈ line) (j,i) * means a (Sum.inl (Sum.inl (Sum.inr j))))
    rw [hseedLine, show means c = means a from funext hm]
  · intro line
    change (∑ z ∈ line ∩ Finset.univ.image growth, (entry c z : ℝ)) -
      (∑ j : Fin P, ∑ i, physicalPairLineWeight growth (fun z => z ∈ line) (j,i) * means c (Sum.inr j)) =
      (∑ z ∈ line ∩ Finset.univ.image growth, (entry a z : ℝ)) -
      (∑ j : Fin P, ∑ i, physicalPairLineWeight growth (fun z => z ∈ line) (j,i) * means a (Sum.inr j))
    rw [hgrowthLine, show means c = means a from funext hm]

end
end Sude
