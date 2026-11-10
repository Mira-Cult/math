import PASoundness.PeanoBitWitnessIntroAll
import PASoundness.PeanoBitWitnessElim
import PASoundness.PeanoPowerUnique
import PASoundness.PeanoPolynomialContext

/-! Forward preservation of an existing bit when the increment is an
explicit multiple of twice that bit's power. -/
namespace PASoundness.PeanoBitMultiplePreserve
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBitPositionReduction

/-- From an explicit literal power and divisibility equation, PA proves that
adding the indicated multiple preserves a set bit. Variables 0,1,5,6,7
are respectively the old code, index, increment, power and multiplier.
This does not derive the divisibility equation or the converse implication. -/
theorem preserve_bit_multiple_vars : FormulaProves
    ((bitFormula (.var 0) (.var 1)).imp
      ((pow2 (.var 1) (.var 6)).imp
        (((.var 5 : Peano.Term).equal (mul (.var 7) (add (.var 6) (.var 6)))).imp
          (bitFormula (add (.var 0) (.var 5)) (.var 1))))) := by
  let A : Peano.Term := .var 0
  let I : Peano.Term := .var 1
  let U : Peano.Term := .var 2
  let Q : Peano.Term := .var 3
  let R : Peano.Term := .var 4
  let D : Peano.Term := .var 5
  let V : Peano.Term := .var 6
  let K : Peano.Term := .var 7
  let P : Peano.Formula := pow2 I U
  let VPower : Peano.Formula := pow2 I V
  let Factor : Peano.Formula := D.equal (mul K (add V V))
  let Target : Peano.Formula := bitFormula (add A D) I
  let Goal : Peano.Formula := VPower.imp (Factor.imp Target)
  have hrow : FormulaProves (row.imp (power.imp Goal)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [Factor, VPower, power, row]
    have hfactor : FOL.Context Peano.Axiom Γ Factor := .head _ _
    have hv : FOL.Context Peano.Axiom Γ VPower := .hypothesis (by simp [Γ])
    have hp : FOL.Context Peano.Axiom Γ P := .hypothesis (by simp [Γ, P, power, I, U, x, p])
    have hrow' : FOL.Context Peano.Axiom Γ row := .hypothesis (by simp [Γ])
    have heq : FOL.Context Peano.Axiom Γ (U.equal V) :=
      .mp (.mp (.closed (PeanoPowerUnique.power_unique I U V)) hp) hv
    have he : FOL.Context Peano.Axiom Γ
        (A.equal (add (add (mul Q (add U U)) U) R)) :=
      FOL.Context.conjunctionLeft hrow'
    have hr : FOL.Context Peano.Axiom Γ (less R U) :=
      FOL.Context.conjunctionRight hrow'
    have hout : FOL.Context Peano.Axiom Γ
        ((add A D).equal (add (add (mul (add Q K) (add U U)) U) R)) := by
      apply PeanoPolynomialContext.cls_exact
      simp only [PeanoPolynomialContext.cls_add, PeanoPolynomialContext.cls_mul]
      have ha := PeanoPolynomialContext.cls_sound he
      have hd := PeanoPolynomialContext.cls_sound hfactor
      have hu := PeanoPolynomialContext.cls_sound heq
      simp only [PeanoPolynomialContext.cls_add, PeanoPolynomialContext.cls_mul] at ha hd
      rw [ha, hd, ← hu]
      ring
    have hw := FOL.Context.conjunctionIntro hout hr
    exact .mp (.mp (.closed (PeanoBitWitnessIntroAll.bit_of_witnesses_all
      (add A D) I U (add Q K) R)) hp) hw
  have hf2 : 2 ∉ Goal.freeVarFinset := by decide
  have hf3 : 3 ∉ Goal.freeVarFinset := by decide
  have hf4 : 4 ∉ Goal.freeVarFinset := by decide
  simpa only [Goal, VPower, Factor, Target, A, I, D, V, K, a, x] using
    PeanoBitWitnessElim.bit_elim Goal hf2 hf3 hf4 hrow

end PASoundness.PeanoBitMultiplePreserve

#print axioms PASoundness.PeanoBitMultiplePreserve.preserve_bit_multiple_vars
