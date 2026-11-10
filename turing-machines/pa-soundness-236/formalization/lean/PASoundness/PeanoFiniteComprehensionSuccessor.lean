import PASoundness.PeanoFiniteCompSelectedMatrix
import PASoundness.PeanoFiniteCompUnselectedMatrix

/-! The literal PA successor step for a bounded selector code. This does not
yet construct the induction base, global support, or the literal AX8 bridge. -/
namespace PASoundness.PeanoFiniteComprehensionSuccessor
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoFiniteComprehensionBase

/-- Both computed successor branches produce the same existential invariant.
Freshness at the power and code names preserves the original selector. -/
theorem selector_successor (φ : Peano.Formula)
    (hφ2 : 2 ∉ φ.freeVarFinset) (hφ3 : 3 ∉ φ.freeVarFinset) :
    FormulaProves ((invariant φ (.var 0)).imp (invariant φ (succ (.var 0)))) :=
  PeanoFiniteComprehensionStepPackage.successor_of_branches φ hφ2 hφ3
    (PeanoFiniteCompSelectedMatrix.selected_matrix φ)
    (PeanoFiniteCompUnselectedMatrix.unselected_matrix φ)

end PASoundness.PeanoFiniteComprehensionSuccessor

#print axioms PASoundness.PeanoFiniteComprehensionSuccessor.selector_successor
