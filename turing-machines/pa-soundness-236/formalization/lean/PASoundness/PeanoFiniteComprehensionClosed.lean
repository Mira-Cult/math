import PASoundness.PeanoFiniteComprehensionInduction
import PASoundness.PeanoFiniteComprehensionSuccessor

/-! PA constructs the bounded selector invariant by induction. The selector
freshness conditions are syntactic; global support and AX8 are separate. -/
namespace PASoundness.PeanoFiniteComprehensionClosed
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoFiniteComprehensionBase

/-- For an arbitrary selector fresh at the induction, power, and code names,
PA proves the bounded-selector invariant at every length. -/
theorem selector_total (φ : Peano.Formula)
    (hφ0 : 0 ∉ φ.freeVarFinset) (hφ2 : 2 ∉ φ.freeVarFinset)
    (hφ3 : 3 ∉ φ.freeVarFinset) :
    FormulaProves (FOL.allAt 0 (invariant φ (.var 0))) :=
  PeanoFiniteComprehensionInduction.induction_of_step φ hφ0 hφ2 hφ3
    (PeanoFiniteComprehensionSuccessor.selector_successor φ hφ2 hφ3)

end PASoundness.PeanoFiniteComprehensionClosed

#print axioms PASoundness.PeanoFiniteComprehensionClosed.selector_total
