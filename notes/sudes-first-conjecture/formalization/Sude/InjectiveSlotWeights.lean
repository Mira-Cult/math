import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

/-! Transfer finite physical labels to distinct allocator slots. -/
namespace Sude
noncomputable section

/-- Extend physical-label weights by zero to the complete slot type. -/
noncomputable def liftedSlotWeight {α β : Type*} [Fintype α] [DecidableEq β]
    (slot : α → β) (weight : α → ℝ) (q : β) : ℝ :=
  ∑ x, if slot x = q then weight x else 0

/-- Injective physical slots recover the exact weight of each label. -/
theorem liftedSlotWeight_at {α β : Type*} [Fintype α] [DecidableEq β]
    (slot : α → β) (hinj : Function.Injective slot) (weight : α → ℝ) (x : α) :
    liftedSlotWeight slot weight (slot x) = weight x := by
  classical
  simp [liftedSlotWeight, hinj.eq_iff]

/-- The slot-indexed squared invoice is exactly the physical-label invoice. -/
theorem liftedSlotWeight_sq_sum {α β : Type*} [Fintype α] [DecidableEq β]
    (slot : α → β) (hinj : Function.Injective slot) (weight : α → ℝ) :
    (∑ q ∈ Finset.univ.image slot, (liftedSlotWeight slot weight q) ^ 2) =
      ∑ x, (weight x) ^ 2 := by
  classical
  rw [Finset.sum_image (by intro x _ y _ h; exact hinj h)]
  simp [liftedSlotWeight_at slot hinj]

end
end Sude
