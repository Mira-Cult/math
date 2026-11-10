import PASoundness.PeanoAX8SelectorLogic
import PASoundness.PeanoAX8SelectorExtraction

/-! Combine bounded selector construction with its AX8-shaped consequences.
The selector bound, the invariant itself, and translation to literal numeric
names remain explicit obligations; this does not assert AX8. -/
namespace PASoundness.PeanoAX8SelectorCombine
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoFiniteComprehensionBase PeanoAX8SelectorLogic PeanoAX8SelectorExtraction

def selectedConsequences (ψ : Peano.Formula) : Peano.Formula :=
  FOL.existsAt 3 (quantifiedGoal ψ ⊓ outerGoal ψ)

/-- The global selector provides one common code satisfying both the
quantified implications and the distinct outer-position implication. -/
theorem global_to_consequences (ψ : Peano.Formula) :
    FormulaProves ((globalExists (selected ψ)).imp (selectedConsequences ψ)) := by
  let A := agreement ψ
  let T := selectedConsequences ψ
  have hbody : FormulaProves (A.imp T) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have ha : FOL.Context Peano.Axiom [A] A := FOL.Context.head [] _
    have hq : FOL.Context Peano.Axiom [A] (quantifiedGoal ψ) :=
      .mp (.closed (quantified_of_agreement ψ)) ha
    have ho : FOL.Context Peano.Axiom [A] (outerGoal ψ) :=
      .mp (.closed (outer_of_agreement ψ)) ha
    have hc : FOL.Context Peano.Axiom [A] (quantifiedGoal ψ ⊓ outerGoal ψ) :=
      FOL.Context.conjunctionIntro hq ho
    have hi : FormulaProves ((quantifiedGoal ψ ⊓ outerGoal ψ).imp T) := by
      simpa only [T, selectedConsequences, SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom)
          (quantifiedGoal ψ ⊓ outerGoal ψ) 3 (.var 3))
    exact .mp (.closed hi) hc
  have hfresh : 3 ∉ T.freeVarFinset := by
    simp [T, selectedConsequences, FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]
  have h := PeanoBitPositionReduction.exists_elim 3 hfresh hbody
  simpa only [A, T, globalExists, globalRows, agreement, output, idx] using h

/-- A bounded invariant and an explicit selector bound yield both
AX8-shaped consequences for the same output code. -/
theorem invariant_to_consequences (ψ : Peano.Formula)
    (hψ2 : 2 ∉ ψ.freeVarFinset) (hψ3 : 3 ∉ ψ.freeVarFinset) :
    FormulaProves ((invariant (selected ψ) (.var 0)).imp
      ((selectorBound (selected ψ)).imp (selectedConsequences ψ))) := by
  have h2 : 2 ∉ (selected ψ).freeVarFinset := by
    have hor : 2 ∉ (bitFormula input idx ⊔ idx.equal outer).freeVarFinset := by decide
    change 2 ∉ (((bitFormula input idx ⊔ idx.equal outer).imp ψ.not).not).freeVarFinset
    simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hor, hψ2]
  have h3 : 3 ∉ (selected ψ).freeVarFinset := by
    have hor : 3 ∉ (bitFormula input idx ⊔ idx.equal outer).freeVarFinset := by decide
    change 3 ∉ (((bitFormula input idx ⊔ idx.equal outer).imp ψ.not).not).freeVarFinset
    simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hor, hψ3]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let I := invariant (selected ψ) (.var 0)
  let S := selectorBound (selected ψ)
  have hi : FOL.Context Peano.Axiom [S,I] I := .hypothesis (by simp)
  have hs : FOL.Context Peano.Axiom [S,I] S := FOL.Context.head _ _
  have hg : FOL.Context Peano.Axiom [S,I] (globalExists (selected ψ)) :=
    .mp (.mp (.closed (invariant_global (selected ψ) h2 h3)) hi) hs
  exact .mp (.closed (global_to_consequences ψ)) hg

end PASoundness.PeanoAX8SelectorCombine

#print axioms PASoundness.PeanoAX8SelectorCombine.global_to_consequences
#print axioms PASoundness.PeanoAX8SelectorCombine.invariant_to_consequences
