import Sude.RegularFactorFlow
import Sude.RegularFactorRF2

/-! Compose the dense-factor and central-stock completion interfaces. -/
namespace Sude
noncomputable section

theorem rowUsed_sdiff {n : ℕ} (E F : Finset (Cell n)) (r : Fin n) :
    LayerPacking.rowUsed (E \ F) r = LayerPacking.rowUsed E r \ LayerPacking.rowUsed F r := by
  ext c
  simp [LayerPacking.rowUsed]

theorem colUsed_sdiff {n : ℕ} (E F : Finset (Cell n)) (c : Fin n) :
    LayerPacking.colUsed (E \ F) c = LayerPacking.colUsed E c \ LayerPacking.colUsed F c := by
  ext r
  simp [LayerPacking.colUsed]

/-- A regular factor leaves at most `t` cells per row and column if the
original residual degrees are at most `k+t`. -/
theorem factor_exception_degrees {n k t : ℕ} (E F : Finset (Cell n))
    (hF : F ⊆ E) (hreg : CellFactorRegular F k)
    (hrow : ∀ r, (LayerPacking.rowUsed E r).card ≤ k + t)
    (hcol : ∀ c, (LayerPacking.colUsed E c).card ≤ k + t) :
    (∀ r, (rowCells r ∩ (E \ F)).card ≤ t) ∧
      (∀ c, (columnCells c ∩ (E \ F)).card ≤ t) := by
  constructor
  · intro r
    rw [factor_row_cells_card, rowUsed_sdiff]
    have hsub : LayerPacking.rowUsed F r ⊆ LayerPacking.rowUsed E r := by
      intro c hc
      simpa [LayerPacking.rowUsed] using hF (by simpa [LayerPacking.rowUsed] using hc)
    have hc := Finset.card_sdiff_add_card_eq_card hsub
    have hr := hreg.1 r
    have hu := hrow r
    omega
  · intro c
    rw [factor_column_cells_card, colUsed_sdiff]
    have hsub : LayerPacking.colUsed F c ⊆ LayerPacking.colUsed E c := by
      intro r hr
      simpa [LayerPacking.colUsed] using hF (by simpa [LayerPacking.colUsed] using hr)
    have hc := Finset.card_sdiff_add_card_eq_card hsub
    have hr := hreg.2 c
    have hu := hcol c
    omega

/-- The RF1 and RF2 finite mechanisms composed on the actual prescribed pool.
This assumes the source degree bounds, a positive factor degree, and an
explicit sufficient central-stock count; it does not establish those inputs
for any controller or prove prime line sums. -/
theorem dense_central_stock_completion {n r Δ : ℕ}
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (hn : 0 < n) (hpositive : (Δ + 1) / 2 < r)
    (hmain : mainCells n ⊆ reserved) (hanti : antiCells n ⊆ reserved)
    (hrowlo : ∀ i, r ≤ (LayerPacking.rowUsed (Finset.univ \ reserved) i).card)
    (hrowhi : ∀ i, (LayerPacking.rowUsed (Finset.univ \ reserved) i).card ≤ r + Δ)
    (hcollo : ∀ i, r ≤ (LayerPacking.colUsed (Finset.univ \ reserved) i).card)
    (hcolhi : ∀ i, (LayerPacking.colUsed (Finset.univ \ reserved) i).card ≤ r + Δ)
    (hdense : 3 * n ≤ 4 * r) (X radius : ℝ) (hrad : 0 ≤ radius)
    (hwidth : ∀ u ∈ actualUnusedPool a reserved, ∀ v ∈ actualUnusedPool a reserved,
      (u.val : ℝ) - (v.val : ℝ) < X)
    (hstock : (Δ + (Δ + 1) / 2) * n ≤ (centralExceptionStock a reserved radius).card) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      (∀ i, |(rowSum b i : ℝ) -
        ((∑ z ∈ rowCells i ∩ reserved, (entry a z : ℝ)) +
          ((rowCells i \ reserved).card : ℝ) *
            centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          X + 2 * (Δ + (Δ + 1) / 2 : ℕ) * radius) ∧
      (∀ i, |(columnSum b i : ℝ) -
        ((∑ z ∈ columnCells i ∩ reserved, (entry a z : ℝ)) +
          ((columnCells i \ reserved).card : ℝ) *
            centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          X + 2 * (Δ + (Δ + 1) / 2 : ℕ) * radius) ∧
      mainSum b = mainSum a ∧ antiSum b = antiSum a ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  classical
  let E := (Finset.univ : Finset (Cell n)) \ reserved
  let k := r - (Δ + 1) / 2
  let t := Δ + (Δ + 1) / 2
  have hk : 0 < k := by dsimp [k]; omega
  have hceil : (Δ + 1) / 2 ≤ r := by omega
  have hkt : k + t = r + Δ := by dsimp [k, t]; omega
  obtain ⟨F, hF, hreg⟩ := dense_residual_regular_factor E hrowlo hrowhi hcollo hcolhi hdense hceil
  have hrow' : ∀ i, (LayerPacking.rowUsed E i).card ≤ k + t := by
    intro i
    rw [hkt]
    exact hrowhi i
  have hcol' : ∀ i, (LayerPacking.colUsed E i).card ≤ k + t := by
    intro i
    rw [hkt]
    exact hcolhi i
  have hreg' : CellFactorRegular F k := hreg
  have hdegrees := factor_exception_degrees (k := k) (t := t) E F hF hreg' hrow' hcol'
  have hbudget := exception_budget_of_row_degrees (E \ F) hdegrees.1
  have hcount : (E \ F).card ≤ (centralExceptionStock a reserved radius).card :=
    hbudget.trans hstock
  exact central_stock_regular_factor_completion a reserved F hF hreg hk hn hmain hanti X radius
    hrad hwidth hcount hdegrees.1 hdegrees.2

end
end Sude
