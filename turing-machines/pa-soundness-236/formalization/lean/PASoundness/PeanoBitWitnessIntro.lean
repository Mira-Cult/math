import PASoundness.PeanoPowerSingleton

/-! Introduction of the literal bit predicate from explicit PA witnesses. -/
namespace PASoundness.PeanoBitWitnessIntro
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

private theorem subst_self (φ : Peano.Formula) (n : Nat) :
    FOL.substAt φ n (.var n) = φ := by
  unfold FOL.substAt
  have hs : (fun y => if y = n then (.var n : Peano.Term) else .var y) = Term.var := by
    funext y
    split <;> simp_all
  rw [hs, SyntaxTransport.formula_subst_var]

def row : Peano.Formula :=
  ((.var 0 : Peano.Term).equal
    (add (add (mul (.var 3) (add (.var 2) (.var 2))) (.var 2)) (.var 4))) ⊓
    less (.var 4) (.var 2)

private def outer : Peano.Formula :=
  (pow2 (.var 1) (.var 2)) ⊓ FOL.existsAt 3 (FOL.existsAt 4 row)

private theorem template_as_bit : bitFormula (.var 0) (.var 1) = bitTemplate := by
  unfold bitFormula
  calc
    bitTemplate.subst (fun y => if y = 0 then .var 0 else if y = 1 then .var 1 else zero) =
        bitTemplate.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro y hy
      simp only [bitTemplate_freeVars, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> rfl
    _ = bitTemplate := SyntaxTransport.formula_subst_var _

/-- For the literal bit template, PA introduces the displayed power, quotient
and remainder witnesses. The witnesses are free in the hypotheses; the result
binds them. This is only the introduction direction and does not establish
existence of the hypotheses or bit insertion. -/
theorem bit_of_witnesses : FormulaProves
    ((pow2 (.var 1) (.var 2)).imp
      (row.imp (bitFormula (.var 0) (.var 1)))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let P := pow2 (.var 1) (.var 2)
  let Γ := [row,P]
  have hr : FOL.Context Peano.Axiom Γ row := .head _ _
  have hp : FOL.Context Peano.Axiom Γ P := .hypothesis (by simp [Γ])
  have hr4 : FOL.Context Peano.Axiom Γ (FOL.existsAt 4 row) := by
    apply FOL.Context.mp (.closed (FOL.Derivation.existsIntro row 4 (.var 4)))
    simpa only [subst_self] using hr
  have hr3 : FOL.Context Peano.Axiom Γ (FOL.existsAt 3 (FOL.existsAt 4 row)) := by
    apply FOL.Context.mp (.closed (FOL.Derivation.existsIntro (FOL.existsAt 4 row) 3 (.var 3)))
    simpa only [subst_self] using hr4
  have ho : FOL.Context Peano.Axiom Γ outer := FOL.Context.conjunctionIntro hp hr3
  have hb : FOL.Context Peano.Axiom Γ (FOL.existsAt 2 outer) := by
    apply FOL.Context.mp (.closed (FOL.Derivation.existsIntro outer 2 (.var 2)))
    simpa only [subst_self] using ho
  change FOL.Context Peano.Axiom Γ (bitFormula (.var 0) (.var 1))
  rw [template_as_bit]
  exact hb

end PASoundness.PeanoBitWitnessIntro

#print axioms PASoundness.PeanoBitWitnessIntro.bit_of_witnesses
