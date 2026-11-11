import Sude.RegularSortedPool

/-! Row and column discrepancy for sorted values on physical matchings. -/
namespace Sude
noncomputable section

def regularRowPick {n : ℕ} (b : Cell n ≃ Fin (n * n))
    (ps : List (Equiv.Perm (Fin n))) (r : Fin n) (j : ℕ) : ℝ :=
  if hj : j < ps.length then (entry b (r, (ps.get ⟨j, hj⟩) r) : ℝ) else 0

def regularColumnPick {n : ℕ} (b : Cell n ≃ Fin (n * n))
    (ps : List (Equiv.Perm (Fin n))) (c : Fin n) (j : ℕ) : ℝ :=
  if hj : j < ps.length then (entry b ((ps.get ⟨j, hj⟩).symm c, c) : ℝ) else 0

/-- Each row takes one actual value from every sorted block. -/
theorem sorted_factor_row_bound {n : ℕ} (b : Cell n ≃ Fin (n * n))
    (ps : List (Equiv.Perm (Fin n))) (values : Finset (pool n))
    (hcard : values.card = ps.length * n) (hk : 0 < ps.length) (hn : 0 < n)
    (hplaced : ∀ x : Fin ps.length × Fin n,
      entry b (regularMatchingSlot ps x) = (sortedFactorValue values hcard x).val)
    (r : Fin n) :
    |(∑ j : Fin ps.length, (entry b (r, (ps.get j) r) : ℝ)) -
      (ps.length : ℝ) * centralEntriesMean values centralPoolValue| ≤
        sortedFactorReal values hcard (ps.length * n - 1) - sortedFactorReal values hcard 0 := by
  have hpick : ∀ j < ps.length, ∃ i < n,
      regularRowPick b ps r j = sortedFactorReal values hcard (j * n + i) := by
    intro j hj
    let J : Fin ps.length := ⟨j, hj⟩
    refine ⟨r.val, r.isLt, ?_⟩
    have hp := congrArg (fun x : ℕ => (x : ℝ)) (hplaced (J, r))
    rw [sortedFactorReal_block values hcard J r]
    simpa [regularRowPick, hj, regularMatchingSlot, J] using hp
  have hb := sortedFactor_blocks_balanced values hcard hk hn (regularRowPick b ps r) hpick
  have hsum : (∑ j ∈ Finset.range ps.length, regularRowPick b ps r j) =
      ∑ j : Fin ps.length, (entry b (r, (ps.get j) r) : ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    simp [regularRowPick, j.isLt]
  rw [hsum] at hb
  exact hb

/-- Each column likewise takes one value from every physical matching block;
the inverse permutation identifies its row. -/
theorem sorted_factor_column_bound {n : ℕ} (b : Cell n ≃ Fin (n * n))
    (ps : List (Equiv.Perm (Fin n))) (values : Finset (pool n))
    (hcard : values.card = ps.length * n) (hk : 0 < ps.length) (hn : 0 < n)
    (hplaced : ∀ x : Fin ps.length × Fin n,
      entry b (regularMatchingSlot ps x) = (sortedFactorValue values hcard x).val)
    (c : Fin n) :
    |(∑ j : Fin ps.length, (entry b ((ps.get j).symm c, c) : ℝ)) -
      (ps.length : ℝ) * centralEntriesMean values centralPoolValue| ≤
        sortedFactorReal values hcard (ps.length * n - 1) - sortedFactorReal values hcard 0 := by
  have hpick : ∀ j < ps.length, ∃ i < n,
      regularColumnPick b ps c j = sortedFactorReal values hcard (j * n + i) := by
    intro j hj
    let J : Fin ps.length := ⟨j, hj⟩
    let r := (ps.get J).symm c
    refine ⟨r.val, r.isLt, ?_⟩
    have hp := congrArg (fun x : ℕ => (x : ℝ)) (hplaced (J, r))
    rw [sortedFactorReal_block values hcard J r]
    simpa [regularColumnPick, hj, regularMatchingSlot, J, r] using hp
  have hb := sortedFactor_blocks_balanced values hcard hk hn (regularColumnPick b ps c) hpick
  have hsum : (∑ j ∈ Finset.range ps.length, regularColumnPick b ps c j) =
      ∑ j : Fin ps.length, (entry b ((ps.get j).symm c, c) : ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    simp [regularColumnPick, j.isLt]
  rw [hsum] at hb
  exact hb

end
end Sude
