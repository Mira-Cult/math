import PASoundness.PeanoFiniteComprehensionLower
import PASoundness.PeanoBitCodeCongruence

/-! Preserve the old membership predicate below the added power's index,
using the selected code in the canonical order `p+a`. -/
namespace PASoundness.PeanoFiniteComprehensionSelectedLower
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- PA preserves both directions of membership at each index below n when
the selected code is `p+a` and p has a literal `2^n` trace. Names 0,1,2,3
are n,i,p,a. This proves the local bit relation; a selector predicate and
its bounded universal filtering invariant are separate obligations. -/
theorem selected_lower_preserved : FormulaProves
    ((pow2 (.var 0) (.var 2)).imp
      ((less (.var 1) (.var 0)).imp
        (((bitFormula (.var 3) (.var 1)).imp
            (bitFormula (add (.var 2) (.var 3)) (.var 1))) ⊓
          ((bitFormula (add (.var 2) (.var 3)) (.var 1)).imp
            (bitFormula (.var 3) (.var 1)))))) := by
  let P := pow2 (.var 0) (.var 2)
  let L := less (.var 1) (.var 0)
  let B := bitFormula (.var 3) (.var 1)
  let R := bitFormula (add (.var 3) (.var 2)) (.var 1)
  let S := bitFormula (add (.var 2) (.var 3)) (.var 1)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Γ := [L,P]
  have hp : FOL.Context Peano.Axiom Γ P := .hypothesis (by simp [Γ])
  have hl : FOL.Context Peano.Axiom Γ L := .head _ _
  have h1 : FOL.Context Peano.Axiom Γ ((B.imp R) ⊓ (R.imp B)) :=
    .mp (.mp (.closed PeanoFiniteComprehensionLower.lower_preserved_add_right) hp) hl
  have h2 : FOL.Context Peano.Axiom Γ ((R.imp S) ⊓ (S.imp R)) :=
    .closed (PeanoBitCodeCongruence.bit_add_comm (.var 3) (.var 2) (.var 1))
  have hb : FOL.Context Peano.Axiom Γ (B.imp S) := by
    apply FOL.Context.deduction
    exact .mp (FOL.Context.under (FOL.Context.conjunctionLeft h2) B)
      (.mp (FOL.Context.under (FOL.Context.conjunctionLeft h1) B) (.head _ _))
  have hs : FOL.Context Peano.Axiom Γ (S.imp B) := by
    apply FOL.Context.deduction
    exact .mp (FOL.Context.under (FOL.Context.conjunctionRight h1) S)
      (.mp (FOL.Context.under (FOL.Context.conjunctionRight h2) S) (.head _ _))
  exact FOL.Context.conjunctionIntro hb hs

end PASoundness.PeanoFiniteComprehensionSelectedLower

#print axioms PASoundness.PeanoFiniteComprehensionSelectedLower.selected_lower_preserved
