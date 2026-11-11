import Sude.FWGrowthCenteredMidpointTransfer

/-! Transfer true-first growth midpoint scores by explicit pairwise
commutativity. This is an algebraic interface for two supplied squares. -/
namespace Sude
noncomputable section

/-- Equal false-first midpoints transfer every true-first weighted, centered
growth score, with exactly the same stage means and weights. -/
theorem fw_growth_true_first_centered_scores_transfer {n L P : ℕ}
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
      ((((entry b (cells (z,true)) : ℝ) + entry b (cells (z,false))) / 2) - μ z.1)) =
    ∑ z : Fin P × Fin (6*(n+8)), w z *
      ((((entry a (cells (z,true)) : ℝ) + entry a (cells (z,false))) / 2) - μ z.1) := by
  classical
  dsimp only
  let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
    offset hoff hs choice gr gc hgr hgc
  change ∀ j i,
    (((entry b (cells ((j,i),false)) : ℝ) + entry b (cells ((j,i),true))) / 2) =
    (((entry a (cells ((j,i),false)) : ℝ) + entry a (cells ((j,i),true))) / 2) at hmid
  apply Finset.sum_congr rfl
  rintro ⟨j,i⟩ _
  have hrev :
      (((entry b (cells ((j,i),true)) : ℝ) + entry b (cells ((j,i),false))) / 2) =
      (((entry a (cells ((j,i),true)) : ℝ) + entry a (cells ((j,i),false))) / 2) := by
    rw [add_comm (entry b (cells ((j,i),true)) : ℝ) (entry b (cells ((j,i),false)) : ℝ),
      add_comm (entry a (cells ((j,i),true)) : ℝ) (entry a (cells ((j,i),false)) : ℝ)]
    exact hmid j i
  rw [hrev]

end
end Sude
