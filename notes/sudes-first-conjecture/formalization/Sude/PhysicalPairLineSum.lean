import Sude.Placement
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Exact line sums over distinct physically placed oriented pairs. -/
namespace Sude
noncomputable section

/-- The number of endpoints of a physical pair lying on a labelled line. -/
noncomputable def physicalPairLineWeight {α : Type*} {n : ℕ}
    (cells : α × Bool → Cell n) (line : Cell n → Prop) (i : α) : ℝ := by
  classical
  exact (if line (cells (i, false)) then 1 else 0) +
    (if line (cells (i, true)) then 1 else 0)

/-- The high-endpoint incidence minus the low-endpoint incidence. -/
noncomputable def physicalPairLineOrientation {α : Type*} {n : ℕ}
    (cells : α × Bool → Cell n) (line : Cell n → Prop) (i : α) : ℝ := by
  classical
  exact (if line (cells (i, true)) then 1 else 0) -
    (if line (cells (i, false)) then 1 else 0)

/-- The actual pair contribution to a labelled line. -/
noncomputable def physicalPairLineContribution {α : Type*} {n : ℕ}
    (cells : α × Bool → Cell n) (line : Cell n → Prop)
    (a : Cell n ≃ Fin (n * n)) (i : α) : ℝ := by
  classical
  exact (if line (cells (i, false)) then (entry a (cells (i, false)) : ℝ) else 0) +
    (if line (cells (i, true)) then (entry a (cells (i, true)) : ℝ) else 0)

/-- A pair's line contribution retains its weighted midpoint and its full
signed half-gap. -/
theorem physicalPairLineContribution_midpoint {α : Type*} {n : ℕ}
    (cells : α × Bool → Cell n) (line : Cell n → Prop)
    (a : Cell n ≃ Fin (n * n)) (i : α) :
    physicalPairLineContribution cells line a i =
      physicalPairLineWeight cells line i *
        (((entry a (cells (i, false)) : ℝ) + entry a (cells (i, true))) / 2) +
      physicalPairLineOrientation cells line i *
        (((entry a (cells (i, true)) : ℝ) - entry a (cells (i, false))) / 2) := by
  classical
  unfold physicalPairLineContribution physicalPairLineWeight physicalPairLineOrientation
  split_ifs <;> ring

/-- For genuinely distinct physical cells, the sum over the actual line
intersection equals the sum of the oriented pair contributions. This does
not include any cells outside the selected pair family. -/
theorem physicalPair_line_sum {α : Type*} [Fintype α] {n : ℕ}
    (cells : α × Bool → Cell n) (hcells : Function.Injective cells)
    (line : Cell n → Prop) [DecidablePred line] (a : Cell n ≃ Fin (n * n)) :
    (∑ c ∈ (Finset.univ.image cells).filter line, (entry a c : ℝ)) =
      ∑ i, physicalPairLineContribution cells line a i := by
  classical
  calc
    _ = ∑ x : α × Bool, if line (cells x) then (entry a (cells x) : ℝ) else 0 := by
      rw [Finset.sum_filter, Finset.sum_image (by intro x _ y _ h; exact hcells h)]
    _ = ∑ i, physicalPairLineContribution cells line a i := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_bool]
      unfold physicalPairLineContribution
      split_ifs <;> ring

/-- The exact selected-cell line sum written entirely in midpoint and
orientation terms. No equal-sum or distinct-line assumption is used. -/
theorem physicalPair_line_sum_midpoint {α : Type*} [Fintype α] {n : ℕ}
    (cells : α × Bool → Cell n) (hcells : Function.Injective cells)
    (line : Cell n → Prop) [DecidablePred line] (a : Cell n ≃ Fin (n * n)) :
    (∑ c ∈ (Finset.univ.image cells).filter line, (entry a c : ℝ)) =
      ∑ i, (physicalPairLineWeight cells line i *
        (((entry a (cells (i, false)) : ℝ) + entry a (cells (i, true))) / 2) +
      physicalPairLineOrientation cells line i *
        (((entry a (cells (i, true)) : ℝ) - entry a (cells (i, false))) / 2)) := by
  rw [physicalPair_line_sum cells hcells line a]
  apply Finset.sum_congr rfl
  intro i _
  exact physicalPairLineContribution_midpoint cells line a i

end
end Sude
