import Sude.BridgeRectangles
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! A square row or column can meet at most one packed rectangle. -/
namespace Sude
noncomputable section

/-- The corner's selected row side, in the packing's Boolean convention. -/
def packedCornerRowSide (corner : Fin 4) : Bool := decide (corner.val < 2)

/-- The corner's selected column side, in the packing's Boolean convention. -/
def packedCornerColumnSide (corner : Fin 4) : Bool := decide (corner.val % 2 = 0)

theorem packedCorner_row_slot {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (j : Fin L) (corner : Fin 4) :
    (packedRectangleCorner hs choice (j, corner)).1 =
      RectanglePacking.rowSlot hs (j, packedCornerRowSide corner) := by
  fin_cases corner <;> rfl

theorem packedCorner_column_slot {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (j : Fin L) (corner : Fin 4) :
    (packedRectangleCorner hs choice (j, corner)).2 =
      RectanglePacking.columnSlot hs choice (j, packedCornerColumnSide corner) := by
  fin_cases corner <;> rfl

/-- Cells on one row cannot come from two different packed rectangles. -/
theorem packedRectangles_same_row {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (j k : Fin L) (a b : Fin 4)
    (h : (packedRectangleCorner hs choice (j, a)).1 =
      (packedRectangleCorner hs choice (k, b)).1) : j = k := by
  rw [packedCorner_row_slot, packedCorner_row_slot] at h
  exact congrArg Prod.fst (RectanglePacking.rowSlot_injective hs h)

/-- Cells on one column cannot come from two different packed rectangles. -/
theorem packedRectangles_same_column {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (j k : Fin L) (a b : Fin 4)
    (h : (packedRectangleCorner hs choice (j, a)).2 =
      (packedRectangleCorner hs choice (k, b)).2) : j = k := by
  rw [packedCorner_column_slot, packedCorner_column_slot] at h
  exact congrArg Prod.fst (RectanglePacking.columnSlot_injective hs choice h)

/-- At most two total endpoint incidences give a squared-weight budget
at most four, including a pair contributing both endpoints. -/
theorem squared_incidence_le_four {ι : Type*} (s : Finset ι) (weight : ι → ℝ)
    (hnonneg : ∀ i ∈ s, 0 ≤ weight i) (hsum : (∑ i ∈ s, weight i) ≤ 2) :
    (∑ i ∈ s, (weight i) ^ 2) ≤ 4 := by
  have hn : 0 ≤ ∑ i ∈ s, weight i := Finset.sum_nonneg hnonneg
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg hnonneg
  have hbound : (∑ i ∈ s, weight i) ^ 2 ≤ (2 : ℝ) ^ 2 :=
    (sq_le_sq₀ hn (by norm_num)).2 hsum
  linarith

end
end Sude
