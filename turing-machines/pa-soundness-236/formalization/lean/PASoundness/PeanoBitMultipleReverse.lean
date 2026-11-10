import PASoundness.PeanoBitWitnessIntroAll
import PASoundness.PeanoBitWitnessElim
import PASoundness.PeanoPowerUnique
import PASoundness.PeanoPowerDoublePositive
import PASoundness.PeanoDivisionWitnessElim
import PASoundness.PeanoRemainderShiftUnique
import PASoundness.PeanoPolynomialContext

/-! Reverse bit preservation under an explicit multiple of the doubled
position power, using PA division and uniqueness of bounded remainders. -/
namespace PASoundness.PeanoBitMultipleReverse
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoBitPositionReduction

/-- PA derives the converse bit-preservation implication under a power trace
and explicit divisibility equation. The variables 0,1,5,6,7,8 denote the
new code, index, old code, increment, multiplier and position power. -/
theorem reverse_multiple_vars : FormulaProves
    ((bitFormula (.var 0) (.var 1)).imp
      ((pow2 (.var 1) (.var 8)).imp
        (((.var 6 : Peano.Term).equal (mul (.var 7) (add (.var 8) (.var 8)))).imp
          (((.var 0 : Peano.Term).equal (add (.var 5) (.var 6))).imp
            (bitFormula (.var 5) (.var 1)))))) := by
  let B : Peano.Term := .var 0
  let I : Peano.Term := .var 1
  let U : Peano.Term := .var 2
  let Q : Peano.Term := .var 3
  let R : Peano.Term := .var 4
  let A : Peano.Term := .var 5
  let D : Peano.Term := .var 6
  let K : Peano.Term := .var 7
  let V : Peano.Term := .var 8
  let H : Peano.Term := .var 9
  let S : Peano.Term := .var 10
  let VP : Peano.Formula := pow2 I V
  let Factor : Peano.Formula := D.equal (mul K (add V V))
  let Eq : Peano.Formula := B.equal (add A D)
  let Target : Peano.Formula := bitFormula A I
  let Goal : Peano.Formula := VP.imp (Factor.imp (Eq.imp Target))
  let Local : Peano.Formula := row.imp (power.imp Goal)
  have hmatrix : FormulaProves (PeanoDivisionWitnessElim.matrix.imp Local) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [Eq, Factor, VP, power, row, PeanoDivisionWitnessElim.matrix]
    have he : FOL.Context Peano.Axiom Γ Eq := .head _ _
    have hf : FOL.Context Peano.Axiom Γ Factor := .hypothesis (by simp [Γ])
    have hv : FOL.Context Peano.Axiom Γ VP := .hypothesis (by simp [Γ])
    have hp : FOL.Context Peano.Axiom Γ (pow2 I U) := .hypothesis (by simp [Γ, power, I, U, x, p])
    have hrow : FOL.Context Peano.Axiom Γ row := .hypothesis (by simp [Γ])
    have hdiv : FOL.Context Peano.Axiom Γ PeanoDivisionWitnessElim.matrix := .hypothesis (by simp [Γ])
    have huv : FOL.Context Peano.Axiom Γ (U.equal V) :=
      .mp (.mp (.closed (PeanoPowerUnique.power_unique I U V)) hp) hv
    have hf' : FOL.Context Peano.Axiom Γ (D.equal (mul K (add U U))) := by
      apply PeanoPolynomialContext.cls_exact
      simp only [PeanoPolynomialContext.cls_mul, PeanoPolynomialContext.cls_add]
      have heq := PeanoPolynomialContext.cls_sound huv
      have hfact := PeanoPolynomialContext.cls_sound hf
      simp only [PeanoPolynomialContext.cls_mul, PeanoPolynomialContext.cls_add] at hfact
      rw [hfact, heq]
    have hdivEq : FOL.Context Peano.Axiom Γ
        (A.equal (add (mul H (add U U)) S)) := FOL.Context.conjunctionLeft hdiv
    have hdivBound : FOL.Context Peano.Axiom Γ (less S (add U U)) :=
      FOL.Context.conjunctionRight hdiv
    have hbitEq : FOL.Context Peano.Axiom Γ
        (B.equal (add (add (mul Q (add U U)) U) R)) := FOL.Context.conjunctionLeft hrow
    have hbound : FOL.Context Peano.Axiom Γ (less R U) := FOL.Context.conjunctionRight hrow
    have hshift : FOL.Context Peano.Axiom Γ
        ((add A D).equal (add (add (mul Q (add U U)) U) R)) :=
      FOL.Context.eqTrans (FOL.Context.eqSymm he) hbitEq
    have hrem : FOL.Context Peano.Axiom Γ (S.equal (add U R)) :=
      .mp (.mp (.mp (.mp (.mp (.closed
        (PeanoRemainderShiftUnique.bit_remainder_shift A D U H K Q S R))
        hdivEq) hf') hshift) hdivBound) hbound
    have hnew : FOL.Context Peano.Axiom Γ
        (A.equal (add (add (mul H (add U U)) U) R)) := by
      apply PeanoPolynomialContext.cls_exact
      simp only [PeanoPolynomialContext.cls_add, PeanoPolynomialContext.cls_mul]
      have heq := PeanoPolynomialContext.cls_sound hdivEq
      have hr := PeanoPolynomialContext.cls_sound hrem
      simp only [PeanoPolynomialContext.cls_add, PeanoPolynomialContext.cls_mul] at heq hr
      rw [heq, hr]
      ring
    exact .mp (.mp (.closed (PeanoBitWitnessIntroAll.bit_of_witnesses_all
      A I U H R)) hp) (FOL.Context.conjunctionIntro hnew hbound)
  have hf9 : 9 ∉ Local.freeVarFinset := by decide
  have hf10 : 10 ∉ Local.freeVarFinset := by decide
  have hdivision := PeanoDivisionWitnessElim.division_elim Local hf9 hf10 hmatrix
  have hlocal : FormulaProves Local := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hp : FOL.Context Peano.Axiom [power,row] (pow2 I U) := by
      simpa [power, I, U, x, p] using (FOL.Context.head [row] power)
    have hd := FOL.Context.mp (.closed (PeanoPowerDoublePositive.division_by_double I U A)) hp
    exact .mp (.mp (.mp (.closed hdivision) hd) (FOL.Context.under (FOL.Context.head [] row) power))
      (FOL.Context.head [row] power)
  have hf2 : 2 ∉ Goal.freeVarFinset := by decide
  have hf3 : 3 ∉ Goal.freeVarFinset := by decide
  have hf4 : 4 ∉ Goal.freeVarFinset := by decide
  simpa only [Goal, VP, Factor, Eq, Target, B, I, A, D, K, V, a, x] using
    PeanoBitWitnessElim.bit_elim Goal hf2 hf3 hf4 hlocal

end PASoundness.PeanoBitMultipleReverse

#print axioms PASoundness.PeanoBitMultipleReverse.reverse_multiple_vars
