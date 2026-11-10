import PASoundness.PeanoBetaAppendRelation
import PASoundness.PeanoBetaAppendCases
import PASoundness.PeanoBetaRowTransfer

/-! PA row preservation when a given CRT code realizes the append relation.
This does not construct that code or assert trace existence. -/
namespace PASoundness.PeanoBetaAppendPreserve
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaAppendRelation

/-- The previous row at output name 20 remains valid for the new code and
parameter, provided a common append-relation row at name 3 is supplied and
index 2 is below the old length `S 0`. The fixed names 0, 2–6, 9 and 20
are distinct; the quantified witness 3 is absent from the conclusion. -/
theorem old_row_preserved : FormulaProves
    ((FOL.existsAt 3 (appendRelation ⊓
      beta (.var 9) (.var 1) (.var 2) (.var 3))).imp
      ((less (.var 2) (succ (.var 0))).imp
        ((beta (.var 4) (.var 5) (.var 2) (.var 20)).imp
          (beta (.var 9) (.var 1) (.var 2) (.var 20))))) := by
  let L := less (.var 2) (succ (.var 0))
  let O := beta (.var 4) (.var 5) (.var 2) (.var 3)
  let N := beta (.var 9) (.var 1) (.var 2) (.var 3)
  let O20 := beta (.var 4) (.var 5) (.var 2) (.var 20)
  let N20 := beta (.var 9) (.var 1) (.var 2) (.var 20)
  let C := FOL.existsAt 3 (O ⊓ N)
  have hf : 3 ∉ (O20.imp N20).freeVarFinset := by decide
  have hbody : FormulaProves ((appendRelation ⊓ N).imp (L.imp (O20.imp N20))) := by
    let Γ := [O20, L, appendRelation ⊓ N]
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hp : FOL.Context Peano.Axiom Γ (appendRelation ⊓ N) := .hypothesis (by simp [Γ])
    have hl : FOL.Context Peano.Axiom Γ L := .hypothesis (by simp [Γ])
    have ho20 : FOL.Context Peano.Axiom Γ O20 := FOL.Context.head _ _
    have hr : FOL.Context Peano.Axiom Γ appendRelation := FOL.Context.conjunctionLeft hp
    have hn : FOL.Context Peano.Axiom Γ N := FOL.Context.conjunctionRight hp
    have ho : FOL.Context Peano.Axiom Γ O := by
      have h := PeanoBetaAppendCases.old_case (.var 2) (succ (.var 0)) O
        ((.var 3 : Peano.Term).equal (add (.var 6) (.var 6)))
      exact .mp (.mp (.closed (by simpa [appendRelation, L, O] using h)) hr) hl
    have hc : FOL.Context Peano.Axiom Γ C := by
      have hintro := FOL.Derivation.existsIntro (A := Peano.Axiom) (O ⊓ N) 3 (.var 3)
      have hi : FormulaProves ((O ⊓ N).imp C) := by
        simpa only [SyntaxTransport.substAt_self, C] using hintro
      exact .mp (.closed hi) (FOL.Context.conjunctionIntro ho hn)
    have htransfer := PeanoBetaRowTransfer.common_output_transfer
      (.var 4) (.var 5) (.var 9) (.var 1) (.var 2) (.var 20) 3 hf
    exact .mp (.mp (.closed htransfer) hc) ho20
  have hfree : 3 ∉ (L.imp (O20.imp N20)).freeVarFinset := by decide
  exact PeanoBitPositionReduction.exists_elim 3 hfree hbody

end PASoundness.PeanoBetaAppendPreserve

#print axioms PASoundness.PeanoBetaAppendPreserve.old_row_preserved
