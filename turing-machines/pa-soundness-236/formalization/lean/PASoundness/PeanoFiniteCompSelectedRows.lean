import PASoundness.PeanoFiniteCompRowsTransport
import PASoundness.PeanoFiniteCompFamilyMerge
import PASoundness.PeanoFiniteCompSelectedBoundary
import PASoundness.PeanoFiniteComprehensionSelected
import PASoundness.PeanoFiniteComprehensionSelectedLower

/-! Filtering rows for the selected case of a bounded selector. -/
namespace PASoundness.PeanoFiniteCompSelectedRows
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoFiniteComprehensionBase

/-- For a selector holding at n, PA extends its old bounded filtering rows
to the selected code `p+a` through `n`, given the old power and code bound.
Names 0, 2, and 3 are n, p, and a; name 1 is the selector's bound index.
The selector may use arbitrary other parameters. This derives the bounded
row family only; witness packaging and the full comprehension theorem are
separate obligations. -/
theorem selected_rows (φ : Peano.Formula) : FormulaProves
    ((pow2 (.var 0) (.var 2)).imp
      ((less (.var 3) (.var 2)).imp
        ((rows φ (.var 0) (.var 3)).imp
          ((FOL.substAt φ 1 (.var 0)).imp
            (rows φ (succ (.var 0)) (add (.var 2) (.var 3))))))) := by
  let P := pow2 (.var 0) (.var 2)
  let L := less (.var 3) (.var 2)
  let R := rows φ (.var 0) (.var 3)
  let F := FOL.substAt φ 1 (.var 0)
  let S := PeanoFiniteCompRowsTransport.sameRows (.var 0) (.var 3)
    (add (.var 2) (.var 3))
  let T := rows φ (.var 0) (add (.var 2) (.var 3))
  let B := bitFormula (add (.var 2) (.var 3)) (.var 0)
  let A := PeanoFiniteCompSelectedBoundary.agreement φ
  have hsame : FormulaProves (P.imp S) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    change FOL.Context Peano.Axiom [P] (FOL.allAt 1
      ((less (.var 1) (.var 0)).imp
        (((bitFormula (.var 3) (.var 1)).imp
            (bitFormula (add (.var 2) (.var 3)) (.var 1))) ⊓
          ((bitFormula (add (.var 2) (.var 3)) (.var 1)).imp
            (bitFormula (.var 3) (.var 1))))))
    apply FOL.Context.generalize 1
    · intro ψ hψ
      simp only [List.mem_singleton] at hψ
      subst ψ
      decide
    exact .mp (.closed PeanoFiniteComprehensionSelectedLower.selected_lower_preserved)
      (.head [] P)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Γ := [F,R,L,P]
  have hp : FOL.Context Peano.Axiom Γ P := .hypothesis (by simp [Γ])
  have hl : FOL.Context Peano.Axiom Γ L := .hypothesis (by simp [Γ])
  have hr : FOL.Context Peano.Axiom Γ R := .hypothesis (by simp [Γ])
  have hf : FOL.Context Peano.Axiom Γ F := .head _ _
  have hs : FOL.Context Peano.Axiom Γ S := .mp (.closed hsame) hp
  have ht : FOL.Context Peano.Axiom Γ T :=
    .mp (.mp (.closed (PeanoFiniteCompRowsTransport.rows_transport φ (.var 0) (.var 3)
      (add (.var 2) (.var 3)))) hr) hs
  have hproperties : FOL.Context Peano.Axiom Γ
      ((pow2 (succ (.var 0)) (add (.var 2) (.var 2))) ⊓
        ((less (add (.var 2) (.var 3)) (add (.var 2) (.var 2))) ⊓ B)) := .mp (.mp (.closed
    PeanoFiniteComprehensionSelected.selected_code_properties) hp) hl
  have hb : FOL.Context Peano.Axiom Γ B :=
    FOL.Context.conjunctionRight (FOL.Context.conjunctionRight hproperties)
  have hboundary : FOL.Context Peano.Axiom Γ (FOL.substAt A 1 (.var 0)) :=
    .mp (.mp (.closed (PeanoFiniteCompSelectedBoundary.selected_boundary φ)) hf) hb
  have hmerge : FOL.Context Peano.Axiom Γ
      (FOL.allAt 1 ((less (.var 1) (succ (.var 0))).imp A)) :=
    .mp (.mp (.closed (PeanoFiniteCompFamilyMerge.merge_family A)) ht) hboundary
  exact hmerge

end PASoundness.PeanoFiniteCompSelectedRows

#print axioms PASoundness.PeanoFiniteCompSelectedRows.selected_rows
