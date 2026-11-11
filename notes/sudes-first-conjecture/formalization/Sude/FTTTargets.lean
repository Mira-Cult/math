import Sude.LucasCertificate

/-! Exact finite target-row properties. The X and T fields are numerals until
separately related to the prescribed prime pool. -/
namespace Sude.Lucas

structure TargetRow where
  order : ℕ
  maxEntry : ℕ
  total : ℕ
  common : ℕ
  penultimate : ℕ
  last : ℕ
  deriving DecidableEq, Repr

def absDiff (a b : ℕ) : ℕ := a - b + (b - a)

/-- Natural subtraction in both directions is the exact integer absolute
value, including either order of the two arguments. -/
theorem absDiff_cast (a b : ℕ) : ((absDiff a b : ℕ) : ℤ) = |(a : ℤ) - b| := by
  by_cases h : a ≤ b
  · rw [absDiff, Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h]
    rw [abs_of_nonpos (by omega)]
    ring
  · have h' : b ≤ a := by omega
    rw [absDiff, Nat.sub_eq_zero_of_le h', add_zero, Nat.cast_sub h']
    rw [abs_of_nonneg (by omega)]

/-- The FTT prime, compatibility, radius and mean claims for one data row.
No assertion here equates its `maxEntry` or `total` to the actual pool. -/
def TargetRowValid (r : TargetRow) : Prop :=
  Nat.Prime r.common ∧ Nat.Prime r.penultimate ∧ Nat.Prime r.last ∧
  3 ≤ r.order ∧ r.order % 2 = 1 ∧
  0 < r.maxEntry ∧ r.maxEntry % 2 = 1 ∧ r.maxEntry < 10 ^ 10 ∧
  r.order * r.order * r.maxEntry < 2 ^ 62 ∧ r.order * r.order < r.maxEntry ∧
  0 < r.total ∧ r.common % 2 = 1 ∧ r.penultimate % 2 = 1 ∧ r.last % 2 = 1 ∧
  (r.order - 2) * r.common + r.penultimate + r.last = r.total ∧
  1000 * absDiff (r.order * r.common) r.total ≤ r.order * r.maxEntry ∧
  1000 * absDiff (r.order * r.penultimate) r.total ≤ r.order * r.maxEntry ∧
  1000 * absDiff (r.order * r.last) r.total ≤ r.order * r.maxEntry ∧
  121 * r.order ^ 2 * r.maxEntry < 250 * r.total ∧
  125 * r.total < 61 * r.order ^ 2 * r.maxEntry

end Sude.Lucas
