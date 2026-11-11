import Sude.StageProbabilityBudget

/-! Translate the source's squared-weight invoice to the probability cap. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
local instance invoicePermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- A bound on the actual stagewise width-squared and weight-squared invoice
implies the sub-Gaussian proxy cap needed by the allocation theorem. -/
theorem stageWeightedProxy_le_of_invoice {r n : ℕ} (slots : Fin r → Finset (Fin n))
    (weights : Fin r → Fin n → ℝ) (lo upper : Fin r → ℝ) (V : ℝ)
    (hlu : ∀ i, lo i ≤ upper i)
    (hnonneg : ∀ i j, j ∈ slots i → 0 ≤ weights i j)
    (hinvoice : (∑ i, (upper i - lo i) ^ 2 * ∑ j ∈ slots i, (weights i j) ^ 2) ≤ V) :
    ((stageWeightedProxy slots weights lo upper : NNReal) : ℝ) ≤ V / 4 := by
  calc
    _ = ∑ i, ((upper i - lo i) ^ 2 / 4) * ∑ j ∈ slots i, (weights i j) ^ 2 :=
      stageWeightedProxy_real slots weights lo upper hlu hnonneg
    _ = (∑ i, (upper i - lo i) ^ 2 * ∑ j ∈ slots i, (weights i j) ^ 2) / 4 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ V / 4 := div_le_div_of_nonneg_right hinvoice (by norm_num)

/-- If each labelled line satisfies the source's squared-weight invoice,
the stage permutations can be chosen to satisfy all its logarithmic bounds. -/
theorem stageLines_exists_of_squared_invoice {m r n : ℕ} (hm : 0 < m)
    (slots : Fin m → Fin r → Finset (Fin n)) (weights : Fin m → Fin r → Fin n → ℝ)
    (values : Fin r → Fin n → ℝ) (lo upper : Fin r → ℝ) (V : ℝ) (hV : 0 ≤ V)
    (hlu : ∀ i, lo i ≤ upper i)
    (hnonneg : ∀ l i j, j ∈ slots l i → 0 ≤ weights l i j)
    (hvalues : ∀ i a, values i a ∈ Set.Icc (lo i) (upper i))
    (hinvoice : ∀ l, (∑ i, (upper i - lo i) ^ 2 * ∑ j ∈ slots l i, (weights l i j) ^ 2) ≤ V) :
    ∃ ω : Fin r → Equiv.Perm (Fin n), ∀ l,
      |stageLineCentered slots weights values l ω| ≤
        Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2) := by
  apply stageLines_exists_of_proxy_cap hm slots weights values lo upper V hV hnonneg hvalues
  intro l
  exact stageWeightedProxy_le_of_invoice (slots l) (weights l) lo upper V hlu (hnonneg l) (hinvoice l)

end
end Sude
