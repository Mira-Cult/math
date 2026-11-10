import PASoundness.PeanoPowerDivisibilityAll
import PASoundness.PeanoPowerDivisibilityClosed

/-! Capture-safe specialization of PA power divisibility. -/
namespace PASoundness.PeanoPowerDivisibilityAllClosed
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoDivisibility

/-- PA derives divisibility of the larger literal power by twice the smaller
literal power whenever the smaller index is strictly less. All arguments are
arbitrary terms and may share variables. -/
theorem power_divisibility (i u n p : Peano.Term) : FormulaProves
    ((pow2 i u).imp ((pow2 n p).imp ((less i n).imp
      (divides (add u u) p)))) :=
  PeanoPowerDivisibilityAll.all_terms_of_fixed
    PeanoPowerDivisibilityClosed.body_proved n i u p

end PASoundness.PeanoPowerDivisibilityAllClosed

#print axioms PASoundness.PeanoPowerDivisibilityAllClosed.power_divisibility
