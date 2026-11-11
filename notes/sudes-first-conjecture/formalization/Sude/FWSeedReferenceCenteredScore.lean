import Sude.StageLineExplicitMean
import Sude.FWSeedExistingReallocation

/-! Transfer the retained-seed centered midpoint score to a supplied fresh
reference, retaining the original grown-square means. Pairwise midpoint
preservation is explicit; no ordered-gap or full-line result is inferred. -/
namespace Sude
noncomputable section

/-- If the ordered square realizes the original grown-square seed permutation
and the same physical pair midpoints pass to a fresh reference, then the
fresh weighted midpoint score equals the original `stageLineCentered` score.
Both the slot weights and the stage means retain their original definitions. -/
theorem fw_seed_reference_centered_score {n L m : ℕ}
    (hseed : 5*(4*6) + 16*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16*3) (hsc : sc.length = 16*3)
    (grown ordered fresh : Cell n ≃ Fin (n*n))
    (ω : Fin 16 → Equiv.Perm (Fin (6*(n+8))))
    (slots : Fin m → Fin 16 → Finset (Fin (6*(n+8))))
    (w : Fin m → Fin 16 → Fin (6*(n+8)) → ℝ)
    (hplaced : ∀ j i side,
      entry ordered (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),side)) =
        entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,ω j i),side)))
    (hmid : ∀ j i,
      (((entry fresh (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) : ℝ) +
          entry fresh (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true))) / 2) =
      (((entry ordered (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) : ℝ) +
          entry ordered (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true))) / 2)) :
    let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let values := fun j i => (((entry grown (cells ((j,i),false)) : ℝ) +
      entry grown (cells ((j,i),true))) / 2)
    ∀ l, stageLineCentered slots w values l ω =
      ∑ j, ∑ i ∈ slots l j, w l j i *
        (((((entry fresh (cells ((j,i),false)) : ℝ) + entry fresh (cells ((j,i),true))) / 2)) -
          ((∑ q, values j q) / (6*(n+8) : ℕ))) := by
  classical
  dsimp only
  let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  let values : Fin 16 → Fin (6*(n+8)) → ℝ := fun j i =>
    (((entry grown (cells ((j,i),false)) : ℝ) + entry grown (cells ((j,i),true))) / 2)
  have hm : ∀ j i,
      (((entry fresh (cells ((j,i),false)) : ℝ) + entry fresh (cells ((j,i),true))) / 2) =
        values j (ω j i) := by
    intro j i
    rw [hmid j i, hplaced j i false, hplaced j i true]
  intro l
  rw [stageLineCentered_eq_explicit_mean (by omega) slots w values l ω]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ i ∈ slots l j, w l j i * values j (ω j i)) -
      (∑ i ∈ slots l j, w l j i) * ((∑ q, values j q) / (6*(n+8) : ℕ)) =
    ∑ i ∈ slots l j, w l j i *
      (((((entry fresh (cells ((j,i),false)) : ℝ) + entry fresh (cells ((j,i),true))) / 2)) -
        ((∑ q, values j q) / (6*(n+8) : ℕ)))
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hm j i]
  ring

end
end Sude
