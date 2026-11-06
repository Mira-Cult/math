import Mathlib.Tactic

namespace Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic

/-- Number of regular two-one cycles until at most two ones remain. -/
def regularCount (m : Nat) : Nat := (m - 1) / 2

/-- Source value at a boundary: `a` counts the left ones and `m` the right ones. -/
def sourceValue (a m : Nat) : Nat := 2 * (a - 1) + m + 1

/-- A physical regular cycle replaces `(a,m)` with `(a+1,m-2)`.
This theorem is arithmetic only, with no reachability or execution assertion. -/
theorem regular_preserves (a m : Nat) (ha : 1 ≤ a) (hm : 2 ≤ m) :
    sourceValue (a + 1) (m - 2) = sourceValue a m := by
  simp only [sourceValue]
  omega

theorem iteration_preserves (a m k : Nat) (ha : 1 ≤ a) (hk : 2 * k ≤ m) :
    sourceValue (a + k) (m - 2 * k) = sourceValue a m := by
  simp only [sourceValue]
  omega

theorem iteration_admissible (m j : Nat) (hj : j < regularCount m) :
    2 * j + 3 ≤ m := by
  simp only [regularCount] at hj
  omega

theorem iteration_within (m j : Nat) (hj : j ≤ regularCount m) :
    2 * j ≤ m := by
  simp only [regularCount] at hj
  omega

theorem terminal_at_most_two (m : Nat) :
    m - 2 * regularCount m ≤ 2 := by
  simp only [regularCount]
  omega

theorem count_positive_iff (m : Nat) : 0 < regularCount m ↔ 3 ≤ m := by
  simp only [regularCount]
  omega

theorem terminal_zero (m : Nat) :
    m - 2 * regularCount m = 0 ↔ m = 0 := by
  simp only [regularCount]
  omega

theorem terminal_one_iff (m : Nat) :
    m - 2 * regularCount m = 1 ↔ m % 2 = 1 := by
  simp only [regularCount]
  omega

theorem terminal_two_iff (m : Nat) :
    m - 2 * regularCount m = 2 ↔ 0 < m ∧ m % 2 = 0 := by
  simp only [regularCount]
  omega

theorem terminal_preserves (a m : Nat) (ha : 1 ≤ a) :
    sourceValue (a + regularCount m) (m - 2 * regularCount m) = sourceValue a m :=
  iteration_preserves a m (regularCount m) ha (iteration_within m _ le_rfl)

/-- The following three calculations classify the arithmetic left to the
separate physical cleanup proofs. They do not assert cleanup execution. -/
theorem case_zero (a : Nat) (ha : 1 ≤ a) :
    sourceValue a 0 = 2 * (a - 1) + 1 ∧ sourceValue a 0 / 2 = a - 1 ∧
      sourceValue a 0 % 2 = 1 := by
  simp only [sourceValue]
  constructor
  · simp
  constructor <;> omega

theorem case_one (a : Nat) (ha : 1 ≤ a) :
    sourceValue a 1 = 2 * a ∧ sourceValue a 1 / 2 = a ∧
      sourceValue a 1 % 2 = 0 := by
  simp only [sourceValue]
  omega

theorem case_two (a : Nat) (ha : 1 ≤ a) :
    sourceValue a 2 = 2 * a + 1 ∧ sourceValue a 2 / 2 = a ∧
      sourceValue a 2 % 2 = 1 := by
  simp only [sourceValue]
  omega

end Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic
