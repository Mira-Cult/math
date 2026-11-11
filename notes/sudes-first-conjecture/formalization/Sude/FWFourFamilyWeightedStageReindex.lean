import Sude.FWGroupedStageMeanReindex

/-! Reindex physical line-weighted original-stage means across the four FW
families, with bridge and wide pairs grouped into their actual double blocks.
No mean bound, allocation, full-line or flow claim is made. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

/-- Grouping two pair slots into each block preserves the line incidence. -/
theorem fw_grouped_stage_line_weight {P n : ℕ}
    (cells : (Fin P × Fin (6 * (n+8))) × Bool → Cell n)
    (line : Cell n → Prop) (j : Fin P) :
    (∑ b : Fin (3 * (n+8)), doubleBlockLineWeight (cells ∘ fwBlockPairIndex P n) line j b) =
      ∑ q, physicalPairLineWeight cells line (j,q) := by
  classical
  calc
    _ = ∑ b : Fin (3 * (n+8)), ∑ p : Fin 2,
        physicalPairLineWeight (cells ∘ fwBlockPairIndex P n) line (j,b,p) := by
      simp [doubleBlockLineWeight, Fin.sum_univ_two]
    _ = ∑ x : Fin (3 * (n+8)) × Fin 2,
        physicalPairLineWeight cells line (j,fwGroupedStagePairEquiv n x) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = _ := Equiv.sum_comp (fwGroupedStagePairEquiv n) (fun q => physicalPairLineWeight cells line (j,q))

/-- The weighted sum over the original four-family stage type is exactly the
sum of bridge and wide grouped weights and seed and growth pair weights. -/
theorem fw_four_family_weighted_stage_reindex {n P L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (line : Cell n → Prop) (m : FWFourStageIndex n P → ℝ) :
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
    (∑ j : FWFourStageIndex n P, ∑ i : Fin (6 * (n+8)),
      physicalPairLineWeight cells line (j,i) * m j) =
      (∑ j : Fin 5, ∑ b : Fin (3 * (n+8)),
        doubleBlockLineWeight (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc) line j b *
          m (Sum.inl (Sum.inl (Sum.inl j)))) +
      (∑ j : Fin 16, ∑ i : Fin (6 * (n+8)),
        physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) line (j,i) *
          m (Sum.inl (Sum.inl (Sum.inr j)))) +
      (∑ j : Fin (3 * (n / 450)), ∑ b : Fin (3 * (n+8)),
        doubleBlockLineWeight (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) line j b *
          m (Sum.inl (Sum.inr j))) +
      (∑ j : Fin P, ∑ i : Fin (6 * (n+8)),
        physicalPairLineWeight (btGrowingOffsetPairCells (Q := 6 * (n+8)) (by omega) (by omega) (by omega)
          (5*(4*6) + 16*(4*6) + (3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
          line (j,i) * m (Sum.inr j)) := by
  classical
  dsimp only
  simp only [FWFourStageIndex, Fintype.sum_sum_type]
  congr 1
  · congr 1
    · congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 1
        exact (fw_grouped_stage_line_weight (fwBridgePhysicalPairCells hrect hs choice br bc hbr hbc) line j).symm
    · apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 1
      exact (fw_grouped_stage_line_weight (fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc) line j).symm

end
end Sude
