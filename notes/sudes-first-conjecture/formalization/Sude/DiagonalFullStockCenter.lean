import Sude.DiagonalFullStockSelection
import Sude.ActualUnusedPool

/-! Choose and physically place a common diagonal center from the full unused
pool. This does not yet bound its effect on every line's expectation. -/
namespace Sude
noncomputable section

/-- If the supplied cell is unreserved and the actual unused pool is nonempty,
place one of its values within half the pool width of its actual mean. The
whole original reservation is preserved, and the new unused pool is exact. -/
theorem actual_unused_pool_place_center {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (center : Cell n) (hcenter : center ∉ reserved)
    (hstock : 0 < (actualUnusedPool a reserved).card) :
    ∃ (b : Cell n ≃ Fin (n * n)) (T : Finset (pool n)),
      T ⊆ actualUnusedPool a reserved ∧ T.card = 1 ∧
      ({center} : Finset (Cell n)).image (entry b) = T.image Subtype.val ∧
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      actualUnusedPool b (reserved ∪ {center}) = actualUnusedPool a reserved \ T ∧
      |(entry b center : ℝ) - centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
        (poolMaximum n : ℝ) / 2 := by
  classical
  have hwidth : ∀ x ∈ actualUnusedPool a reserved, ∀ y ∈ actualUnusedPool a reserved,
      centralPoolValue y - centralPoolValue x ≤ (poolMaximum n : ℝ) := by
    intro x hx y hy
    exact le_of_lt (actual_unused_pool_strict_width a reserved y hy x hx)
  obtain ⟨T, hT, hTc, herr⟩ := full_stock_label_select (actualUnusedPool a reserved)
    centralPoolValue 1 (poolMaximum n : ℝ) (by positivity) (by omega) hwidth
  have hav : ∀ v ∈ T, ∀ z ∈ reserved, v.val ≠ entry a z := by
    intro v hv z hz
    exact actualUnusedPool_avoids a reserved v (hT hv) z hz
  have hdisj : Disjoint ({center} : Finset (Cell n)) reserved := by simpa using hcenter
  obtain ⟨b, himage, hfixed, _, _⟩ := place_finite_population a {center} T reserved
    (by simpa using hTc) hdisj hav
  have hremain := actualUnusedPool_after_placement a b reserved {center} T hfixed himage
  have hsum := finite_population_sum b {center} T himage
  refine ⟨b, T, hT, hTc, himage, hfixed, hremain, ?_⟩
  have hsum' : (entry b center : ℝ) = ∑ v ∈ T, centralPoolValue v := by simpa using hsum
  rw [← hsum'] at herr
  simpa using herr

end
end Sude
