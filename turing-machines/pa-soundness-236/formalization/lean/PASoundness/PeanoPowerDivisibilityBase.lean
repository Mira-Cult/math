import PASoundness.PeanoEmptyBitSet
import PASoundness.PeanoDivisibility

/-! The zero-index base case of a proposed power divisibility induction. -/
namespace PASoundness.PeanoPowerDivisibilityBase
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- Capture-safe divisibility at the free names 2 and 6. -/
def divisible : Peano.Formula := PeanoDivisibility.divides
  (add (.var 2) (.var 2)) (.var 6)

/-- The unquantified zero-index implication is derivable in PA, because
there is no index strictly below zero. No power-divisibility step is used. -/
theorem zero_case : FormulaProves
    ((pow2 (.var 1) (.var 2)).imp
      ((pow2 zero (.var 6)).imp ((less (.var 1) zero).imp divisible))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hbad : FOL.Context Peano.Axiom
      [less (.var 1) zero, pow2 zero (.var 6), pow2 (.var 1) (.var 2)]
      (less (.var 1) zero) := .head _ _
  exact FOL.Context.explode divisible
    (.mp (.closed (PeanoEmptyBitSet.no_less_zero (.var 1))) hbad)

/-- The same base is universally closed over its three remaining variables. -/
theorem zero_case_quantified : FormulaProves (FOL.allAt 1 (FOL.allAt 2 (FOL.allAt 6
    ((pow2 (.var 1) (.var 2)).imp
      ((pow2 zero (.var 6)).imp ((less (.var 1) zero).imp divisible)))))) :=
  .generalize 1 (.generalize 2 (.generalize 6 zero_case))

end PASoundness.PeanoPowerDivisibilityBase

#print axioms PASoundness.PeanoPowerDivisibilityBase.zero_case
#print axioms PASoundness.PeanoPowerDivisibilityBase.zero_case_quantified
