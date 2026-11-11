import Sude.RegularFactorLines
import Sude.CentralDiagonalPlacement

/-! Complete a supplied regular residual factor with the actual unused pool.
Factor existence and the earlier exceptional-cell placement are separate obligations. -/
namespace Sude
noncomputable section

/-- Sorted matching blocks fill every unreserved cell exactly once. The row and
column discrepancies are strictly less than the supplied width of the actual
unused pool, relative to the fixed entries plus the residual-pool mean. -/
theorem sorted_regular_factor_completion {n k : ℕ}
    (a : Cell n ≃ Fin (n * n)) (reserved E : Finset (Cell n))
    (hfree : E = Finset.univ \ reserved) (hreg : CellFactorRegular E k)
    (hk : 0 < k) (hn : 0 < n)
    (hmain : mainCells n ⊆ reserved) (hanti : antiCells n ⊆ reserved)
    (X : ℝ)
    (hwidth : ∀ u ∈ actualUnusedPool a reserved, ∀ v ∈ actualUnusedPool a reserved,
      (u.val : ℝ) - (v.val : ℝ) < X) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      (∀ r, |(rowSum b r : ℝ) -
        ((∑ z ∈ rowCells r ∩ reserved, (entry a z : ℝ)) +
          (k : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| < X) ∧
      (∀ c, |(columnSum b c : ℝ) -
        ((∑ z ∈ columnCells c ∩ reserved, (entry a z : ℝ)) +
          (k : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| < X) ∧
      mainSum b = mainSum a ∧ antiSum b = antiSum a ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  classical
  obtain ⟨ps, hlen, hdec, hcard, b, hplaced, hfixed, _, _, hpool, hinj⟩ :=
    place_sorted_regular_factor a reserved E hfree hreg
  have hkps : 0 < ps.length := by omega
  have hlenReal : (ps.length : ℝ) = (k : ℝ) := by exact_mod_cast hlen
  have hpositive : 0 < ps.length * n := Nat.mul_pos hkps hn
  have hlast : ps.length * n - 1 < ps.length * n := by omega
  have hmax := (actualUnusedPool a reserved).orderEmbOfFin_mem hcard
    ⟨ps.length * n - 1, hlast⟩
  have hmin := (actualUnusedPool a reserved).orderEmbOfFin_mem hcard ⟨0, hpositive⟩
  have hspread : sortedFactorReal (actualUnusedPool a reserved) hcard (ps.length * n - 1) -
      sortedFactorReal (actualUnusedPool a reserved) hcard 0 < X := by
    simpa [sortedFactorReal, hlast, hpositive] using hwidth _ hmax _ hmin
  refine ⟨b, hfixed, ?_, ?_, ?_, ?_, hpool, hinj⟩
  · intro r
    have hrow : (rowSum b r : ℝ) =
        (∑ z ∈ rowCells r ∩ reserved, (entry a z : ℝ)) +
          ∑ j : Fin ps.length, (entry b (r, (ps.get j) r) : ℝ) := by
      rw [rowSum_real_cells, central_line_fixed_parts a b (rowCells r) reserved hfixed,
        regularFactor_row_sum hdec hfree]
    have hdiff : (rowSum b r : ℝ) -
        ((∑ z ∈ rowCells r ∩ reserved, (entry a z : ℝ)) +
          (k : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue) =
        (∑ j : Fin ps.length, (entry b (r, (ps.get j) r) : ℝ)) -
          (ps.length : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue := by
      rw [hrow, hlenReal]
      ring
    rw [hdiff]
    exact (sorted_factor_row_bound b ps (actualUnusedPool a reserved) hcard hkps hn hplaced r).trans_lt hspread
  · intro c
    have hcol : (columnSum b c : ℝ) =
        (∑ z ∈ columnCells c ∩ reserved, (entry a z : ℝ)) +
          ∑ j : Fin ps.length, (entry b ((ps.get j).symm c, c) : ℝ) := by
      rw [columnSum_real_cells, central_line_fixed_parts a b (columnCells c) reserved hfixed,
        regularFactor_column_sum hdec hfree]
    have hdiff : (columnSum b c : ℝ) -
        ((∑ z ∈ columnCells c ∩ reserved, (entry a z : ℝ)) +
          (k : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue) =
        (∑ j : Fin ps.length, (entry b ((ps.get j).symm c, c) : ℝ)) -
          (ps.length : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue := by
      rw [hcol, hlenReal]
      ring
    rw [hdiff]
    exact (sorted_factor_column_bound b ps (actualUnusedPool a reserved) hcard hkps hn hplaced c).trans_lt hspread
  · unfold mainSum
    apply Finset.sum_congr rfl
    intro i _
    exact hfixed _ (hmain (by simp))
  · unfold antiSum
    apply Finset.sum_congr rfl
    intro i _
    exact hfixed _ (hanti (by simp))

end
end Sude
