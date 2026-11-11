import Sude.FWGroupedStageMeanReindex
import Sude.DoubleBlockProtectedLogReallocation

/-! Exact same-ordered-square bridge and wide midpoint score alignment.
The old and ordered squares and side-preserving block reallocations remain
explicit. No score bound, complement, full-line or later-flow claim. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

/-- A grouped score centered at source means is the original pair-slot
weighted midpoint deviation from the same ordered square's stage means. -/
theorem fw_grouped_score_ordered_mean {n P : ℕ}
    (cells : (Fin P × Fin (6 * (n+8))) × Bool → Cell n)
    (line : Cell n → Prop) (old new : Cell n ≃ Fin (n*n))
    (π : Fin P → Equiv.Perm (Fin (3*(n+8)))) (s : Fin P → Fin (3*(n+8)) → Bool)
    (hentry : ∀ j b p side, entry new ((cells ∘ fwBlockPairIndex P n) ((j,b,p),side)) =
      entry old ((cells ∘ fwBlockPairIndex P n) ((j,π j b,doubleBlockPairSwap (s j b) p),side))) :
    doubleBlockActualCenteredScore (cells ∘ fwBlockPairIndex P n) line old new =
      ∑ j, ∑ q, physicalPairLineWeight cells line (j,q) *
        ((((entry new (cells ((j,q),false)) : ℝ) + entry new (cells ((j,q),true))) / 2) -
          (∑ i, (((entry new (cells ((j,i),false)) : ℝ) + entry new (cells ((j,i),true))) / 2)) /
            ((6*(n+8) : ℕ) : ℝ)) := by
  classical
  let grouped := cells ∘ fwBlockPairIndex P n
  have hmean (j : Fin P) : doubleStageMidpointMean grouped old j =
      (∑ i, (((entry new (cells ((j,i),false)) : ℝ) + entry new (cells ((j,i),true))) / 2)) /
        ((6*(n+8) : ℕ) : ℝ) := by
    rw [← (double_block_stage_midpoint_mean_preserved grouped old new π s hentry j).2]
    exact (fw_grouped_stage_midpoint_mean cells new j).symm
  change doubleBlockActualCenteredScore grouped line old new = _
  unfold doubleBlockActualCenteredScore
  simp_rw [hmean]
  have hw (j : Fin P) (b : Fin (3*(n+8))) (p : Fin 2) :
      physicalPairLineWeight grouped line (j,b,p) =
        physicalPairLineWeight cells line (j,fwGroupedStagePairEquiv n (b,p)) := by
    unfold physicalPairLineWeight grouped fwBlockPairIndex fwGroupedStagePairEquiv
    rfl
  simp_rw [hw]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← (fwGroupedStagePairEquiv n).sum_comp (fun q : Fin (6*(n+8)) =>
    physicalPairLineWeight cells line (j,q) *
      ((((entry new (cells ((j,q),false)) : ℝ) + entry new (cells ((j,q),true))) / 2) -
        (∑ i, (((entry new (cells ((j,i),false)) : ℝ) + entry new (cells ((j,i),true))) / 2)) /
          ((6*(n+8) : ℕ) : ℝ)))]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Fin.sum_univ_two, doubleBlockLineWeight, doubleBlockPairMidpoint, hw]
  dsimp [grouped, fwGroupedStagePairEquiv, fwBlockPairIndex]
  simp only [finCongr_apply]
  ring

/-- The old double-block baseline is the same unsquared physical pair-weighted
baseline computed from each stage's actual mean on the ordered square. -/
theorem fw_grouped_baseline_ordered_mean {n P : ℕ}
    (cells : (Fin P × Fin (6 * (n+8))) × Bool → Cell n)
    (line : Cell n → Prop) (old new : Cell n ≃ Fin (n*n))
    (π : Fin P → Equiv.Perm (Fin (3*(n+8)))) (s : Fin P → Fin (3*(n+8)) → Bool)
    (hentry : ∀ j b p side, entry new ((cells ∘ fwBlockPairIndex P n) ((j,b,p),side)) =
      entry old ((cells ∘ fwBlockPairIndex P n) ((j,π j b,doubleBlockPairSwap (s j b) p),side)))
    (j : Fin P) :
    (∑ b, doubleBlockLineWeight (cells ∘ fwBlockPairIndex P n) line j b *
      doubleStageMidpointMean (cells ∘ fwBlockPairIndex P n) old j) =
    ∑ q, physicalPairLineWeight cells line (j,q) *
      ((∑ i, (((entry new (cells ((j,i),false)) : ℝ) + entry new (cells ((j,i),true))) / 2)) /
        ((6*(n+8) : ℕ) : ℝ)) := by
  classical
  let grouped := cells ∘ fwBlockPairIndex P n
  have hmean : doubleStageMidpointMean grouped old j =
      (∑ i, (((entry new (cells ((j,i),false)) : ℝ) + entry new (cells ((j,i),true))) / 2)) /
        ((6*(n+8) : ℕ) : ℝ) := by
    rw [← (double_block_stage_midpoint_mean_preserved grouped old new π s hentry j).2]
    exact (fw_grouped_stage_midpoint_mean cells new j).symm
  have hw (b : Fin (3*(n+8))) (p : Fin 2) :
      physicalPairLineWeight grouped line (j,b,p) =
        physicalPairLineWeight cells line (j,fwGroupedStagePairEquiv n (b,p)) := by
    unfold physicalPairLineWeight grouped fwBlockPairIndex fwGroupedStagePairEquiv
    rfl
  change (∑ b, doubleBlockLineWeight grouped line j b * doubleStageMidpointMean grouped old j) = _
  rw [hmean, ← (fwGroupedStagePairEquiv n).sum_comp (fun q : Fin (6*(n+8)) =>
    physicalPairLineWeight cells line (j,q) *
      ((∑ i, (((entry new (cells ((j,i),false)) : ℝ) + entry new (cells ((j,i),true))) / 2)) /
        ((6*(n+8) : ℕ) : ℝ)))]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [doubleBlockLineWeight, hw, Fin.sum_univ_two]
  ring

/-- Actual bridge and wide source baselines and centered scores align with
original FW four-family means on the same ordered square. -/
theorem fw_bridge_wide_ordered_mean_scores {n P L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (old new : Cell n ≃ Fin (n*n))
    (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8)))) (sb : Fin 5 → Fin (3 * (n + 8)) → Bool)
    (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (sw : Fin (3 * (n / 450)) → Fin (3 * (n + 8)) → Bool)
    (hbridge : ∀ j b p side, entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,b,p),side)) =
      entry old (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,πb j b,doubleBlockPairSwap (sb j b) p),side)))
    (hwideEntry : ∀ j b p side, entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),side)) =
      entry old (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,πw j b,doubleBlockPairSwap (sw j b) p),side)))
    (line : Cell n → Prop) :
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
    let mean := fun j : FWFourStageIndex n P =>
      (∑ q, (((entry new (cells ((j,q),false)) : ℝ) + entry new (cells ((j,q),true))) / 2)) /
        ((6*(n+8) : ℕ) : ℝ)
    let midpoint := fun j q => (((entry new (cells ((j,q),false)) : ℝ) +
      entry new (cells ((j,q),true))) / 2)
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    doubleBlockActualCenteredScore bridge line old new =
      (∑ j : Fin 5, ∑ q, physicalPairLineWeight cells line (Sum.inl (Sum.inl (Sum.inl j)),q) *
        (midpoint (Sum.inl (Sum.inl (Sum.inl j))) q - mean (Sum.inl (Sum.inl (Sum.inl j))))) ∧
    doubleBlockActualCenteredScore wide line old new =
      (∑ j : Fin (3 * (n / 450)), ∑ q, physicalPairLineWeight cells line (Sum.inl (Sum.inr j),q) *
        (midpoint (Sum.inl (Sum.inr j)) q - mean (Sum.inl (Sum.inr j)))) ∧
    (∀ j : Fin 5, (∑ b, doubleBlockLineWeight bridge line j b * doubleStageMidpointMean bridge old j) =
      ∑ q, physicalPairLineWeight cells line (Sum.inl (Sum.inl (Sum.inl j)),q) *
        mean (Sum.inl (Sum.inl (Sum.inl j)))) ∧
    (∀ j : Fin (3 * (n / 450)), (∑ b, doubleBlockLineWeight wide line j b * doubleStageMidpointMean wide old j) =
      ∑ q, physicalPairLineWeight cells line (Sum.inl (Sum.inr j),q) * mean (Sum.inl (Sum.inr j))) := by
  classical
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fw_grouped_score_ordered_mean (fwBridgePhysicalPairCells hrect hs choice br bc hbr hbc)
      line old new πb sb hbridge
  · exact fw_grouped_score_ordered_mean (fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc)
      line old new πw sw hwideEntry
  · intro j
    exact fw_grouped_baseline_ordered_mean (fwBridgePhysicalPairCells hrect hs choice br bc hbr hbc)
      line old new πb sb hbridge j
  · intro j
    exact fw_grouped_baseline_ordered_mean (fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc)
      line old new πw sw hwideEntry j

end
end Sude
