import PASoundness.PeanoFiniteCompUnselectedBoundary
import PASoundness.PeanoFiniteCompUnselected
import PASoundness.PeanoFiniteCompFamilyMerge

/-! Bounded selector rows for the branch retaining the old code. -/
namespace PASoundness.PeanoFiniteCompUnselectedRows
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoFiniteComprehensionBase

/-- If the selector is false at the old endpoint, PA extends the old
bounded agreement family to `S n` with the same code. The power and bound
premises are used to prove the old endpoint bit is absent. -/
theorem unselected_rows (φ : Peano.Formula) : FormulaProves
    ((pow2 (.var 0) (.var 2)).imp
      ((less (.var 3) (.var 2)).imp
        ((rows φ (.var 0) (.var 3)).imp
          ((FOL.substAt φ 1 (.var 0)).not.imp
            (rows φ (succ (.var 0)) (.var 3)))))) := by
  let P := pow2 (.var 0) (.var 2)
  let L := less (.var 3) (.var 2)
  let R := rows φ (.var 0) (.var 3)
  let N := (FOL.substAt φ 1 (.var 0)).not
  let A := PeanoFiniteCompUnselectedBoundary.agreement φ
  let Γ := [N,R,L,P]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hp : FOL.Context Peano.Axiom Γ P := .hypothesis (by simp [Γ])
  have hl : FOL.Context Peano.Axiom Γ L := .hypothesis (by simp [Γ])
  have hr : FOL.Context Peano.Axiom Γ R := .hypothesis (by simp [Γ])
  have hn : FOL.Context Peano.Axiom Γ N := .head _ _
  have hs := FOL.Context.conjunctionRight
    (FOL.Context.conjunctionRight (.mp (.mp (.closed PeanoFiniteCompUnselected.unselected_step) hp) hl))
  have hb : FOL.Context Peano.Axiom Γ (FOL.substAt A 1 (.var 0)) :=
    .mp (.mp (.closed (PeanoFiniteCompUnselectedBoundary.unselected_boundary φ)) hn) hs
  have hmerge := PeanoFiniteCompFamilyMerge.merge_family A
  change FormulaProves (R.imp ((FOL.substAt A 1 (.var 0)).imp
    (rows φ (succ (.var 0)) (.var 3)))) at hmerge
  exact .mp (.mp (.closed hmerge) hr) hb

end PASoundness.PeanoFiniteCompUnselectedRows

#print axioms PASoundness.PeanoFiniteCompUnselectedRows.unselected_rows
