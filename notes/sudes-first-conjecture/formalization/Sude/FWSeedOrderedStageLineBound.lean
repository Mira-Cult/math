import Sude.FWSeedSourceStageMeanAlignment
import Sude.FWSeedStageOrientationZero

/-! A supplied seed deviation invoice uses the original grown-square means.
Align those means to the same ordered square and cancel the actual seed
orientation on physical rows and columns. No allocation or full-line bound
is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

/-- The ordered seed line contribution obeys the supplied error bound around
its actual same-ordered-square four-family stage means. The stage permutation
and the grown-source deviation invoices are explicit inputs. -/
theorem fw_seed_ordered_stage_line_bound {n P L : ℕ}
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
    (hrow : ∀ r : Fin n,
      let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      let values := fun j i => (((entry grown (cells ((j,i),false)) : ℝ) +
          entry grown (cells ((j,i),true))) / 2)
      |(∑ z ∈ (Finset.univ.image cells).filter (fun z => z.1 = r), (entry ordered z : ℝ)) -
        (∑ j, ((∑ i, physicalPairLineWeight cells (fun z => z.1 = r) (j,i)) *
          ((∑ i, values j i) / ((6*(n+8) : ℕ) : ℝ)))) -
        (∑ p, physicalPairLineOrientation cells (fun z => z.1 = r) p * ((2 : ℝ) / 2))| ≤ B)
    (hcol : ∀ c : Fin n,
      let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      let values := fun j i => (((entry grown (cells ((j,i),false)) : ℝ) +
          entry grown (cells ((j,i),true))) / 2)
      |(∑ z ∈ (Finset.univ.image cells).filter (fun z => z.2 = c), (entry ordered z : ℝ)) -
        (∑ j, ((∑ i, physicalPairLineWeight cells (fun z => z.2 = c) (j,i)) *
          ((∑ i, values j i) / ((6*(n+8) : ℕ) : ℝ)))) -
        (∑ p, physicalPairLineOrientation cells (fun z => z.2 = c) p * ((2 : ℝ) / 2))| ≤ B) :
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
  classical
  dsimp only
  have hm := fw_seed_source_stage_mean_alignment hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc grown ordered ω hplaced
  dsimp only at hm
  constructor
  · intro r
    have hb := fw_seed_row_deviation_without_orientation hseed hs choice sr sc hsr hsc ordered
      (∑ j, ((∑ i, physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun z => z.1 = r) (j,i)) *
        ((∑ i, (((entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) : ℝ) +
          entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true))) / 2)) /
          ((6*(n+8) : ℕ) : ℝ)))) B r (hrow r)
    dsimp only at hb
    convert hb using 1
    congr 2
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_mul, hm j]
  · intro c
    have hb := fw_seed_column_deviation_without_orientation hseed hs choice sr sc hsr hsc ordered
      (∑ j, ((∑ i, physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun z => z.2 = c) (j,i)) *
        ((∑ i, (((entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) : ℝ) +
          entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true))) / 2)) /
          ((6*(n+8) : ℕ) : ℝ)))) B c (hcol c)
    dsimp only at hb
    convert hb using 1
    congr 2
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_mul, hm j]

end
end Sude
