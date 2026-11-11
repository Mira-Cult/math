import Sude.DenseCentralCompletion
import Sude.PoolWidth

/-! RF3's integer parameter substitutions and residual degree geometry. -/
namespace Sude
noncomputable section

/-- A reserved-cell complement has exactly the missing row and column slots. -/
theorem rowUsed_complement {n : ℕ} (reserved : Finset (Cell n)) (i : Fin n) :
    LayerPacking.rowUsed (Finset.univ \ reserved) i = Finset.univ \ LayerPacking.rowUsed reserved i := by
  ext j
  simp [LayerPacking.rowUsed]

theorem colUsed_complement {n : ℕ} (reserved : Finset (Cell n)) (i : Fin n) :
    LayerPacking.colUsed (Finset.univ \ reserved) i = Finset.univ \ LayerPacking.colUsed reserved i := by
  ext j
  simp [LayerPacking.colUsed]

/-- RF3's exact natural-number arithmetic, including the subtraction and
ceiling in the factor degree. -/
theorem balanced_factor_parameters (n r₀ b : ℕ) (hload : 4 * (r₀ + 6 * b + 4) ≤ n) :
    let Δ := 6 * b + 4
    let r := n - r₀ - Δ
    3 * n ≤ 4 * r ∧ (Δ + 1) / 2 < r ∧
      r - (Δ + 1) / 2 = n - r₀ - (9 * b + 6) ∧
      Δ + (Δ + 1) / 2 = 9 * b + 6 := by
  dsimp
  omega

/-- Occupancy bounds translate to the two-sided residual degree bounds used
in RF1, with exact cardinalities of physical row and column cells. -/
theorem balanced_residual_degrees {n r₀ b : ℕ} (reserved : Finset (Cell n))
    (hload : 4 * (r₀ + 6 * b + 4) ≤ n)
    (hrowlo : ∀ i, r₀ ≤ (LayerPacking.rowUsed reserved i).card)
    (hrowhi : ∀ i, (LayerPacking.rowUsed reserved i).card ≤ r₀ + (6 * b + 4))
    (hcollo : ∀ i, r₀ ≤ (LayerPacking.colUsed reserved i).card)
    (hcolhi : ∀ i, (LayerPacking.colUsed reserved i).card ≤ r₀ + (6 * b + 4)) :
    let Δ := 6 * b + 4
    let r := n - r₀ - Δ
    (∀ i, r ≤ (LayerPacking.rowUsed (Finset.univ \ reserved) i).card ∧
      (LayerPacking.rowUsed (Finset.univ \ reserved) i).card ≤ r + Δ) ∧
    (∀ i, r ≤ (LayerPacking.colUsed (Finset.univ \ reserved) i).card ∧
      (LayerPacking.colUsed (Finset.univ \ reserved) i).card ≤ r + Δ) := by
  dsimp
  constructor
  · intro i
    rw [rowUsed_complement]
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (LayerPacking.rowUsed reserved i))
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    have hlo := hrowlo i
    have hhi := hrowhi i
    omega
  · intro i
    rw [colUsed_complement]
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (LayerPacking.colUsed reserved i))
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    have hlo := hcollo i
    have hhi := hcolhi i
    omega

/-- RF3's dense central completion with its actual degree parameter and a
stock count. The free pool has strict width below its own largest prime;
no extra analytic premise is needed for that fact. This theorem assumes the
controller's stated physical occupancy and stock inequalities. -/
theorem balanced_residual_central_completion {n r₀ b : ℕ}
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (hmain : mainCells n ⊆ reserved) (hanti : antiCells n ⊆ reserved)
    (hload : 4 * (r₀ + 6 * b + 4) ≤ n)
    (hrowlo : ∀ i, r₀ ≤ (LayerPacking.rowUsed reserved i).card)
    (hrowhi : ∀ i, (LayerPacking.rowUsed reserved i).card ≤ r₀ + (6 * b + 4))
    (hcollo : ∀ i, r₀ ≤ (LayerPacking.colUsed reserved i).card)
    (hcolhi : ∀ i, (LayerPacking.colUsed reserved i).card ≤ r₀ + (6 * b + 4))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hstock : (9 * b + 6) * n ≤
      (centralExceptionStock a reserved (ε * poolMaximum n)).card) :
    ∃ c : Cell n ≃ Fin (n * n),
      (∀ z ∈ reserved, entry c z = entry a z) ∧
      (∀ i, |(rowSum c i : ℝ) -
        ((∑ z ∈ rowCells i ∩ reserved, (entry a z : ℝ)) +
          ((rowCells i \ reserved).card : ℝ) *
            centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          (1 + 2 * (9 * b + 6 : ℕ) * ε) * poolMaximum n) ∧
      (∀ i, |(columnSum c i : ℝ) -
        ((∑ z ∈ columnCells i ∩ reserved, (entry a z : ℝ)) +
          ((columnCells i \ reserved).card : ℝ) *
            centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          (1 + 2 * (9 * b + 6 : ℕ) * ε) * poolMaximum n) ∧
      mainSum c = mainSum a ∧ antiSum c = antiSum a ∧
      Set.range (entry c) = pool n ∧ Function.Injective (entry c) := by
  let Δ := 6 * b + 4
  let r := n - r₀ - Δ
  have hn : 0 < n := by omega
  have hparam : 3 * n ≤ 4 * r ∧ (Δ + 1) / 2 < r ∧
      r - (Δ + 1) / 2 = n - r₀ - (9 * b + 6) ∧
      Δ + (Δ + 1) / 2 = 9 * b + 6 := balanced_factor_parameters n r₀ b hload
  have hdeg := balanced_residual_degrees reserved hload hrowlo hrowhi hcollo hcolhi
  have hstock' : (Δ + (Δ + 1) / 2) * n ≤
      (centralExceptionStock a reserved (ε * poolMaximum n)).card := by
    rw [hparam.2.2.2]
    exact hstock
  have hrad : 0 ≤ ε * (poolMaximum n : ℝ) := mul_nonneg hε (by positivity)
  have h := dense_central_stock_completion (r := r) (Δ := Δ) a reserved hn hparam.2.1 hmain hanti
    (fun i => (hdeg.1 i).1) (fun i => (hdeg.1 i).2)
    (fun i => (hdeg.2 i).1) (fun i => (hdeg.2 i).2)
    hparam.1 (poolMaximum n) (ε * poolMaximum n) hrad
    (actual_unused_pool_strict_width a reserved) hstock'
  rw [hparam.2.2.2] at h
  have heq : (poolMaximum n : ℝ) + 2 * (9 * b + 6 : ℕ) * (ε * poolMaximum n) =
      (1 + 2 * (9 * b + 6 : ℕ) * ε) * poolMaximum n := by ring
  simpa only [heq] using h

end
end Sude
