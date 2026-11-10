import PASoundness.PeanoBitMultipleReverse
import PASoundness.PeanoDivisibility

/-! Reverse bit preservation under an existential divisibility premise. -/
namespace PASoundness.PeanoBitDivisibleReverse
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoDivisibility

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private def quotientRow : Peano.Formula :=
  (.var 6 : Peano.Term).equal (mul (.var 7) (add (.var 2) (.var 2)))

private theorem divides_syntax :
    divides (add (.var 2) (.var 2)) (.var 6) = FOL.existsAt 7 quotientRow := by
  simp [divides, dividesTemplate, quotientRow, FOL.existsAt, FOL.allAt,
    Peano.mul, Peano.add, Peano.zero, FirstOrder.Language.Term.equal,
    FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst,
    FirstOrder.Language.Term.relabel, FirstOrder.Language.BoundedFormula.not,
    FirstOrder.Language.BoundedFormula.subst, FirstOrder.Language.BoundedFormula.relabel,
    FirstOrder.Language.BoundedFormula.mapTermRel, FirstOrder.Language.BoundedFormula.relabelAux]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

private def relation (b u : Peano.Term) : Peano.Formula :=
  (bitFormula b (.var 1)).imp
    ((pow2 (.var 1) u).imp
      (((.var 6 : Peano.Term).equal (mul (.var 7) (add u u))).imp
        ((b.equal (add (.var 5) (.var 6))).imp (bitFormula (.var 5) (.var 1)))))

private theorem fixed_quotient : FormulaProves
    ((bitFormula (add (.var 5) (.var 6)) (.var 1)).imp
      ((pow2 (.var 1) (.var 2)).imp
        (quotientRow.imp (bitFormula (.var 5) (.var 1))))) := by
  have hv : FormulaProves (relation (.var 0) (.var 8)) :=
    PeanoBitMultipleReverse.reverse_multiple_vars
  have h8 := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (relation (.var 0) (.var 8)) 8 (.var 2)))
    (.generalize 8 hv)
  have h8' : FormulaProves (relation (.var 0) (.var 2)) := by
    simpa [FOL.substAt, relation, subst_imp, bitFormula_subst, pow2_subst,
      FOL.equality_subst, PeanoArithmetic.add_subst, PeanoMultiplication.mul_subst,
      FirstOrder.Language.Term.subst] using h8
  have h0 := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom)
      (.allElim (relation (.var 0) (.var 2)) 0 (add (.var 5) (.var 6))))
    (.generalize 0 h8')
  have h0' : FormulaProves (relation (add (.var 5) (.var 6)) (.var 2)) := by
    simpa [FOL.substAt, relation, subst_imp, bitFormula_subst, pow2_subst,
      FOL.equality_subst, PeanoArithmetic.add_subst, PeanoMultiplication.mul_subst,
      FirstOrder.Language.Term.subst] using h0
  let B := bitFormula (add (.var 5) (.var 6)) (.var 1)
  let P := pow2 (.var 1) (.var 2)
  let T := bitFormula (.var 5) (.var 1)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Γ := [quotientRow, P, B]
  have hb : FOL.Context Peano.Axiom Γ B := .hypothesis (by simp [Γ])
  have hp : FOL.Context Peano.Axiom Γ P := .hypothesis (by simp [Γ])
  have hq : FOL.Context Peano.Axiom Γ quotientRow := .head _ _
  have heq : FOL.Context Peano.Axiom Γ
      ((add (.var 5) (.var 6)).equal (add (.var 5) (.var 6))) :=
    .closed (.logical (.eqRefl _))
  exact .mp (.mp (.mp (.mp (.closed h0') hb) hp) hq) heq

/-- PA preserves bit membership in the reverse direction under a
divisibility premise: if the increment is divisible by twice the displayed
position power, a bit in the new code was already present in the old code.
The power trace and divisibility are premises, not established here. -/
theorem reverse_bit_of_divides : FormulaProves
    ((divides (add (.var 2) (.var 2)) (.var 6)).imp
      ((pow2 (.var 1) (.var 2)).imp
        ((bitFormula (add (.var 5) (.var 6)) (.var 1)).imp
          (bitFormula (.var 5) (.var 1))))) := by
  let P := pow2 (.var 1) (.var 2)
  let B := bitFormula (add (.var 5) (.var 6)) (.var 1)
  let T := bitFormula (.var 5) (.var 1)
  let G := P.imp (B.imp T)
  have hr : FormulaProves (quotientRow.imp G) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [B,P,quotientRow]
    have hb : FOL.Context Peano.Axiom Γ B := .head _ _
    have hp : FOL.Context Peano.Axiom Γ P := .hypothesis (by simp [Γ])
    have he : FOL.Context Peano.Axiom Γ quotientRow := .hypothesis (by simp [Γ])
    exact .mp (.mp (.mp (.closed fixed_quotient) hb) hp) he
  have hf : 7 ∉ G.freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 7 hf hr
  simpa only [divides_syntax, G, P, B, T] using h

end PASoundness.PeanoBitDivisibleReverse

#print axioms PASoundness.PeanoBitDivisibleReverse.reverse_bit_of_divides
