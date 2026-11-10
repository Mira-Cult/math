import PASoundness.PeanoBetaAppendRelation
import PASoundness.PeanoBetaAppendCases
import PASoundness.PeanoBetaRowTransfer

/-! PA boundary-row extraction from a supplied append-relation recoding.
This does not construct the code or assert trace existence. -/
namespace PASoundness.PeanoBetaAppendBoundary
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaAppendRelation

/-- At index `S n`, any supplied recoding row has the appended output `p+p`.
The witness 3 is absent from the displayed conclusion, so it can be eliminated
without capturing the old or new code, their parameters, the index, or `p`. -/
theorem boundary_row : FormulaProves
    ((FOL.existsAt 3 (appendRelation ⊓
      beta (.var 9) (.var 1) (.var 2) (.var 3))).imp
      (((.var 2 : Peano.Term).equal (succ (.var 0))).imp
        (beta (.var 9) (.var 1) (.var 2) (add (.var 6) (.var 6))))) := by
  let E : Peano.Formula := (.var 2 : Peano.Term).equal (succ (.var 0))
  let O := beta (.var 4) (.var 5) (.var 2) (.var 3)
  let N := beta (.var 9) (.var 1) (.var 2) (.var 3)
  let V := (.var 3 : Peano.Term).equal (add (.var 6) (.var 6))
  let T := beta (.var 9) (.var 1) (.var 2) (add (.var 6) (.var 6))
  have hbody : FormulaProves ((appendRelation ⊓ N).imp (E.imp T)) := by
    let Γ := [E, appendRelation ⊓ N]
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hp : FOL.Context Peano.Axiom Γ (appendRelation ⊓ N) := .hypothesis (by simp [Γ])
    have he : FOL.Context Peano.Axiom Γ E := FOL.Context.head _ _
    have hr : FOL.Context Peano.Axiom Γ appendRelation := FOL.Context.conjunctionLeft hp
    have hn : FOL.Context Peano.Axiom Γ N := FOL.Context.conjunctionRight hp
    have hv : FOL.Context Peano.Axiom Γ V := by
      have h := PeanoBetaAppendCases.new_case (.var 2) (succ (.var 0)) O V
      exact .mp (.mp (.closed (by simpa [appendRelation, E, O, V] using h)) hr) he
    exact .mp (.mp (.closed (PeanoBetaRowTransfer.beta_output_congr
      (.var 9) (.var 1) (.var 2) (.var 3) (add (.var 6) (.var 6)))) hv) hn
  have hfree : 3 ∉ (E.imp T).freeVarFinset := by decide
  exact PeanoBitPositionReduction.exists_elim 3 hfree hbody

end PASoundness.PeanoBetaAppendBoundary

#print axioms PASoundness.PeanoBetaAppendBoundary.boundary_row
