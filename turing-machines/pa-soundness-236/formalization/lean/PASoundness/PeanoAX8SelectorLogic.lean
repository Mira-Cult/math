import PASoundness.PeanoFiniteComprehensionBase

/-! Propositional consequences of a global finite selector.

This fixed-name PA derivation retains the selected outer position separately
from the universally bound index. Instantiating the decoded AX8 predicate and
handling its name collisions remain separate obligations. -/
namespace PASoundness.PeanoAX8SelectorLogic
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

def input : Peano.Term := .var 4
def output : Peano.Term := .var 3
def idx : Peano.Term := .var 1
def outer : Peano.Term := .var 5

def selected (ψ : Peano.Formula) : Peano.Formula :=
  (bitFormula input idx ⊔ idx.equal outer) ⊓ ψ

def agreement (ψ : Peano.Formula) : Peano.Formula := FOL.allAt 1
  (((bitFormula output idx).imp (selected ψ)) ⊓
    ((selected ψ).imp (bitFormula output idx)))

def quantifiedGoal (ψ : Peano.Formula) : Peano.Formula := FOL.allAt 1
  (((bitFormula input idx).imp (ψ.imp (bitFormula output idx))) ⊓
    ((bitFormula output idx).imp ψ))

def outerGoal (ψ : Peano.Formula) : Peano.Formula :=
  (FOL.substAt ψ 1 outer).imp (bitFormula output outer)

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl
private theorem subst_and (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊓ ψ).subst σ = (φ.subst σ) ⊓ (ψ.subst σ) := by
  change (φ.imp ψ.not).not.subst σ = ((φ.subst σ).imp (ψ.subst σ).not).not
  rw [subst_not, show (φ.imp ψ.not).subst σ = (φ.subst σ).imp (ψ.not.subst σ) from rfl, subst_not]
private theorem subst_or (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊔ ψ).subst σ = (φ.subst σ) ⊔ (ψ.subst σ) := by
  change (φ.not.imp ψ).subst σ = (φ.subst σ).not.imp (ψ.subst σ)
  rw [show (φ.not.imp ψ).subst σ = (φ.not.subst σ).imp (ψ.subst σ) from rfl, subst_not]
private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

/-- The exact selector gives both literal quantified implications, without
requiring any freshness property of the parameter formula. -/
theorem quantified_of_agreement (ψ : Peano.Formula) :
    FormulaProves ((agreement ψ).imp (quantifiedGoal ψ)) := by
  let B := bitFormula output idx
  let A := bitFormula input idx
  let E := idx.equal outer
  let S := (A ⊔ E) ⊓ ψ
  let H := agreement ψ
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.generalize 1
  · intro f hf
    simp only [List.mem_singleton] at hf
    subst f
    simp [agreement, SyntaxTransport.allAt_freeVars]
  · have hg : FOL.Context Peano.Axiom [H] ((B.imp S) ⊓ (S.imp B)) := by
      simpa only [H, agreement, selected, B, A, E, S] using
        (FOL.Context.allSelf (FOL.Context.head [] H))
    have hf : FOL.Context Peano.Axiom [H] (A.imp (ψ.imp B)) := by
      apply FOL.Context.deduction
      apply FOL.Context.deduction
      have ha : FOL.Context Peano.Axiom [ψ,A,H] A := .hypothesis (by simp)
      have hψ : FOL.Context Peano.Axiom [ψ,A,H] ψ := FOL.Context.head _ _
      have ho : FOL.Context Peano.Axiom [ψ,A,H] (A ⊔ E) := by
        apply FOL.Context.deduction
        exact FOL.Context.explode E (.mp (FOL.Context.head _ _) (FOL.Context.under ha _))
      have hs : FOL.Context Peano.Axiom [ψ,A,H] S := FOL.Context.conjunctionIntro ho hψ
      exact .mp (FOL.Context.under (FOL.Context.under (FOL.Context.conjunctionRight hg) A) ψ) hs
    have hb : FOL.Context Peano.Axiom [H] (B.imp ψ) := by
      apply FOL.Context.deduction
      have hs : FOL.Context Peano.Axiom [B,H] S :=
        .mp (FOL.Context.under (FOL.Context.conjunctionLeft hg) B) (FOL.Context.head _ _)
      exact FOL.Context.conjunctionRight hs
    exact FOL.Context.conjunctionIntro hf hb

/-- The distinguished outer position is selected independently of input
membership, so agreement entails the separate outer implication. -/
theorem outer_of_agreement (ψ : Peano.Formula) :
    FormulaProves ((agreement ψ).imp (outerGoal ψ)) := by
  let G := agreement ψ
  let X := FOL.substAt ψ 1 outer
  let B := bitFormula output outer
  let A := bitFormula input outer
  let E := outer.equal outer
  let S := (A ⊔ E) ⊓ X
  have hinst : FormulaProves (G.imp ((B.imp S) ⊓ (S.imp B))) := by
    have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
      (.allElim (((bitFormula output idx).imp (selected ψ)) ⊓
        ((selected ψ).imp (bitFormula output idx))) 1 outer)
    simpa [G, agreement, S, A, E, B, X, selected, input, output, idx, outer,
      FOL.substAt, subst_and, subst_or, subst_imp, bitFormula_subst, FOL.equality_subst,
      FirstOrder.Language.Term.subst] using h
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hψ : FOL.Context Peano.Axiom [X,G] X := FOL.Context.head _ _
  have hg : FOL.Context Peano.Axiom [X,G] G := .hypothesis (by simp)
  have he : FOL.Context Peano.Axiom [X,G] E := .closed (.logical (.eqRefl outer))
  have ho : FOL.Context Peano.Axiom [X,G] (A ⊔ E) := by
    apply FOL.Context.deduction
    exact FOL.Context.under he _
  have hs : FOL.Context Peano.Axiom [X,G] S := FOL.Context.conjunctionIntro ho hψ
  exact .mp (FOL.Context.conjunctionRight (.mp (.closed hinst) hg)) hs

end PASoundness.PeanoAX8SelectorLogic

#print axioms PASoundness.PeanoAX8SelectorLogic.quantified_of_agreement
#print axioms PASoundness.PeanoAX8SelectorLogic.outer_of_agreement
