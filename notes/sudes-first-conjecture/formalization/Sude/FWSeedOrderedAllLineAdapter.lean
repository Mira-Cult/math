import Sude.FWSeedOrderedStageLineBound
import Sude.FWGrowthOrdinaryRecenterLineBound

/-! Specialize one supplied all-physical-lines seed invoice to actual rows
and columns, keeping the same source and ordered square. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

theorem fw_seed_ordered_stage_line_bound_of_all_lines {n P L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (grown ordered : Cell n ≃ Fin (n*n))
    (ω : Fin 16 → Equiv.Perm (Fin (6*(n+8)))) (B : ℝ)
    (hplaced : ∀ j i side,
      entry ordered (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),side)) =
        entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,ω j i),side)))
    (hline : ∀ l : Fin ((n+n)+2),
      let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      let line := fun z => z ∈ physicalAllLineCells l
      let values := fun j i => (((entry grown (cells ((j,i),false)) : ℝ) +
          entry grown (cells ((j,i),true))) / 2)
      |(∑ z ∈ (Finset.univ.image cells).filter line, (entry ordered z : ℝ)) -
        (∑ j, ((∑ i, physicalPairLineWeight cells line (j,i)) *
          ((∑ i, values j i) / ((6*(n+8) : ℕ) : ℝ)))) -
        (∑ p, physicalPairLineOrientation cells line p * ((2 : ℝ) / 2))| ≤ B) :
    let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
    let means := fun j : FWFourStageIndex n P =>
      (∑ i, (((entry ordered (cells ((j,i),false)) : ℝ) + entry ordered (cells ((j,i),true))) / 2)) /
        ((6 * (n+8) : ℕ) : ℝ)
    (∀ r : Fin n, |(∑ z ∈ (Finset.univ.image seed).filter (fun z => z.1 = r), (entry ordered z : ℝ)) -
      (∑ j : Fin 16, ∑ i, physicalPairLineWeight seed (fun z => z.1 = r) (j,i) *
        means (Sum.inl (Sum.inl (Sum.inr j))))| ≤ B) ∧
    (∀ c : Fin n, |(∑ z ∈ (Finset.univ.image seed).filter (fun z => z.2 = c), (entry ordered z : ℝ)) -
      (∑ j : Fin 16, ∑ i, physicalPairLineWeight seed (fun z => z.2 = c) (j,i) *
        means (Sum.inl (Sum.inl (Sum.inr j))))| ≤ B) := by
  apply fw_seed_ordered_stage_line_bound hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc grown ordered ω B hplaced
  · intro r
    simpa only [fwGrowthRowLineLabel, physicalAllLineCells, Equiv.symm_apply_apply, mem_rowCells] using
      hline (fwGrowthRowLineLabel r)
  · intro c
    simpa only [fwGrowthColumnLineLabel, physicalAllLineCells, Equiv.symm_apply_apply, mem_columnCells] using
      hline (fwGrowthColumnLineLabel c)

end
end Sude
