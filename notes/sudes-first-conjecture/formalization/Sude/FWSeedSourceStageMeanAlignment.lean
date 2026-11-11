import Sude.FWFourFamilyStageTotals
import Sude.FWSeedExistingReallocation

/-! Align retained-seed means on an ordered square with their original source
means. The supplied equations identify the same original stage and one
permutation of its pairs. No placement, theta, or line bound is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- If every endpoint on the ordered square is a stage-preserving permutation
of the grown-square seed endpoints, then each four-family seed stage has the
same midpoint mean on the two squares. -/
theorem fw_seed_source_stage_mean_alignment {n P L : ℕ}
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
    (ω : Fin 16 → Equiv.Perm (Fin (6*(n+8))))
    (hplaced : ∀ j i side,
      entry ordered (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),side)) =
        entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,ω j i),side))) :
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
    let means := fun a (j : FWFourStageIndex n P) =>
      (∑ i, (((entry a (cells ((j,i),false)) : ℝ) + entry a (cells ((j,i),true))) / 2)) /
        ((6 * (n + 8) : ℕ) : ℝ)
    ∀ j : Fin 16, means ordered (Sum.inl (Sum.inl (Sum.inr j))) =
      (∑ i, (((entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) : ℝ) +
        entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true))) / 2)) /
        ((6 * (n + 8) : ℕ) : ℝ) := by
  classical
  dsimp only
  intro j
  change (∑ i, (((entry ordered (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) : ℝ) +
    entry ordered (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true))) / 2)) /
      ((6 * (n + 8) : ℕ) : ℝ) = _
  let f : Fin (6*(n+8)) → ℝ := fun i =>
    (((entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) : ℝ) +
      entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true))) / 2)
  have hsum : (∑ i, (((entry ordered (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) : ℝ) +
      entry ordered (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true))) / 2)) = ∑ i, f i := by
    calc
      _ = ∑ i, f (ω j i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [f, hplaced]
      _ = ∑ i, f i := Equiv.sum_comp (ω j) f
  rw [hsum]

end
end Sude
