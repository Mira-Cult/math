import PASoundness.PeanoPowerDivisibilityInduction
import PASoundness.PeanoPowerDivisibilityStep
import PASoundness.PeanoPowerDivisibilityBoundary

/-! The predecessor-witness core of the power-divisibility successor step. -/
namespace PASoundness.PeanoPowerDivisibilityCore
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoDivisibility
open PeanoPowerDivisibilityInduction PeanoCommonMultiple.DivisibilityBoundary

private theorem or_elim {L : Language} {A : FOL.Formula L → Prop}
    {Γ : List (FOL.Formula L)} {φ ψ χ : FOL.Formula L}
    (h : FOL.Context A Γ (φ ⊔ ψ)) (hφ : FOL.Context A Γ (φ.imp χ))
    (hψ : FOL.Context A Γ (ψ.imp χ)) : FOL.Context A Γ χ := by
  apply FOL.Context.dne
  apply FOL.Context.deduction
  have hnφ : FOL.Context A (χ.not :: Γ) φ.not :=
    .mp (FOL.Context.under (FOL.Context.contrapose hφ) χ.not) (FOL.Context.head Γ χ.not)
  have hψ' : FOL.Context A (χ.not :: Γ) ψ := .mp (FOL.Context.under h χ.not) hnφ
  exact .mp (FOL.Context.head Γ χ.not) (.mp (FOL.Context.under hψ χ.not) hψ')

/-- Given the explicitly displayed predecessor power and its doubling
equation, the induction family implies the successor divisibility result.
The family-instantiation derivation is an explicit premise; this theorem
does not construct or eliminate the predecessor witness. -/
theorem successor_from_predecessor
    (hinst : FormulaProves (family.imp
      ((pow2 (.var 1) (.var 2)).imp ((pow2 (.var 0) (.var 8)).imp
        ((less (.var 1) (.var 0)).imp (divides (add (.var 2) (.var 2)) (.var 8))))))) :
    FormulaProves (family.imp ((pow2 (.var 1) (.var 2)).imp
      ((pow2 (.var 0) (.var 8)).imp
        (((.var 6 : Peano.Term).equal (add (.var 8) (.var 8))).imp
          ((less (.var 1) (succ (.var 0))).imp
            (divides (add (.var 2) (.var 2)) (.var 6))))))) := by
  let I : Peano.Term := .var 1
  let N : Peano.Term := .var 0
  let U : Peano.Term := .var 2
  let R : Peano.Term := .var 8
  let P : Peano.Term := .var 6
  let HU := pow2 I U
  let HR := pow2 N R
  let HE := P.equal (add R R)
  let HL := less I (succ N)
  let EQ := I.equal N
  let LT := less I N
  let D := divides (add U U) P
  let Γ := [HL, HE, HR, HU, family]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hf : FOL.Context Peano.Axiom Γ family := .hypothesis (by simp [Γ])
  have hu : FOL.Context Peano.Axiom Γ HU := .hypothesis (by simp [Γ])
  have hr : FOL.Context Peano.Axiom Γ HR := .hypothesis (by simp [Γ])
  have he : FOL.Context Peano.Axiom Γ HE := .hypothesis (by simp [Γ])
  have hl : FOL.Context Peano.Axiom Γ HL := .head _ _
  have hs : FOL.Context Peano.Axiom Γ (EQ ⊔ LT) :=
    .mp (.closed (PeanoCommonMultiple.BoundSplit.less_successor_cases I N)) hl
  have hEq : FOL.Context Peano.Axiom Γ (EQ.imp D) := by
    apply FOL.Context.deduction
    exact .mp (.mp (.mp (.mp
      (.closed (PeanoPowerDivisibilityBoundary.equal_index_divides I N U R P))
      (.head _ _)) (FOL.Context.under hu EQ)) (FOL.Context.under hr EQ))
        (FOL.Context.under he EQ)
  have hLt : FOL.Context Peano.Axiom Γ (LT.imp D) := by
    apply FOL.Context.deduction
    let Γ' := LT :: Γ
    have hdiv : FOL.Context Peano.Axiom Γ' (divides (add U U) R) :=
      .mp (.mp (.mp (.mp (.closed hinst) (FOL.Context.under hf LT))
        (FOL.Context.under hu LT)) (FOL.Context.under hr LT)) (.head _ _)
    have hdouble : FOL.Context Peano.Axiom Γ' (divides (add U U) (add R R)) :=
      .mp (.closed (PeanoPowerDivisibilityStep.divides_double (add U U) R)) hdiv
    exact .mp (.mp (.closed (dividend_congr (add U U) (add R R) P))
      (FOL.Context.eqSymm (FOL.Context.under he LT))) hdouble
  exact or_elim hs hEq hLt

end PASoundness.PeanoPowerDivisibilityCore

#print axioms PASoundness.PeanoPowerDivisibilityCore.successor_from_predecessor
