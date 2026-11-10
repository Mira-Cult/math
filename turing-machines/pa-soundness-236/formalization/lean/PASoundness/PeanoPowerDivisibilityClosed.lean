import PASoundness.PeanoPowerDivisibilityCompose
import PASoundness.PeanoPowerDivisibilitySuccessorOpen

/-! Closed PA induction for divisibility between power traces. -/
namespace PASoundness.PeanoPowerDivisibilityClosed
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoPowerDivisibilityInduction

/-- PA proves the universally quantified power-divisibility family. -/
theorem family_proved : FormulaProves (FOL.allAt 0 family) :=
  PeanoPowerDivisibilityCompose.family_of_open_successor
    PeanoPowerDivisibilitySuccessorOpen.successor_open

/-- For the fixed free names n=0, i=1, u=2, p=6, PA derives
pow2(i,u) → pow2(n,p) → i<n → divides(u+u,p). -/
theorem body_proved : FormulaProves (body (.var 0)) :=
  PeanoPowerDivisibilityCompose.body_of_open_successor
    PeanoPowerDivisibilitySuccessorOpen.successor_open

end PASoundness.PeanoPowerDivisibilityClosed

#print axioms PASoundness.PeanoPowerDivisibilityClosed.family_proved
#print axioms PASoundness.PeanoPowerDivisibilityClosed.body_proved
