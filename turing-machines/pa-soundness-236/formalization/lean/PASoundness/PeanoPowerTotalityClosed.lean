import PASoundness.PeanoPowerTotality
import PASoundness.PeanoPowerAppendSuccessor

/-! PA totality of literal beta-coded doubling traces, combining the checked
trace-extension derivation with the PA induction theorem. -/
namespace PASoundness.PeanoPowerTotalityClosed
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic

/-- PA derives that every index has a beta-coded doubling trace. -/
theorem power_total : FormulaProves
    (FOL.allAt 0 PeanoPowerTotality.existsPower) :=
  PeanoPowerTotality.totality_of_successor PeanoPowerAppendSuccessor.power_successor

end PASoundness.PeanoPowerTotalityClosed

#print axioms PASoundness.PeanoPowerTotalityClosed.power_total
