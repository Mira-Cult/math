import Sude.FWGrowthPairMidpointTransfer

/-! Transfer a fixed-reference growth midpoint score once pairwise midpoint
preservation has been established on the same two squares. -/
namespace Sude
noncomputable section

/-- Any fixed stage means and fixed weights give identical centered midpoint
scores on two supplied squares with equal actual growth-pair midpoints. -/
theorem fw_growth_centered_midpoint_scores_transfer {n L P : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (gr gc : List (LayerPacking.Layer n))
    (hgr : gr.length = P*3) (hgc : gc.length = P*3)
    (a b : Cell n ≃ Fin (n*n)) (w : Fin P × Fin (6*(n+8)) → ℝ) (μ : Fin P → ℝ)
    (hmid : ∀ j i,
      (((entry b (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
          offset hoff hs choice gr gc hgr hgc ((j,i),false)) : ℝ) +
        entry b (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
          offset hoff hs choice gr gc hgr hgc ((j,i),true))) / 2) =
      (((entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
          offset hoff hs choice gr gc hgr hgc ((j,i),false)) : ℝ) +
        entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
          offset hoff hs choice gr gc hgr hgc ((j,i),true))) / 2)) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc
    (∑ z : Fin P × Fin (6*(n+8)), w z *
      ((((entry b (cells (z,false)) : ℝ) + entry b (cells (z,true))) / 2) - μ z.1)) =
    ∑ z : Fin P × Fin (6*(n+8)), w z *
      ((((entry a (cells (z,false)) : ℝ) + entry a (cells (z,true))) / 2) - μ z.1) := by
  classical
  dsimp only
  apply Finset.sum_congr rfl
  rintro ⟨j,i⟩ _
  rw [hmid j i]

end
end Sude
