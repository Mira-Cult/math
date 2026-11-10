import PASoundness.PeanoAX8CanonicalClosed
import PASoundness.PeanoAX8PredicateNormalize
import PASoundness.PeanoAX8AllAlpha

/-! Exact canonical-name AX8-shaped formula for an arbitrary fresh predicate.
Instantiation with the decoded predicate and transport to arbitrary names are
separate obligations; this module does not assert full AX8. -/
namespace PASoundness.PeanoAX8CanonicalFormula
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoAX8SelectorLogic PeanoAX8SelectorCombine
open PeanoAX8PredicateNormalize

/-- The exact canonical quantified implications and separate outer-index
implication share the same existential code at name 3. -/
def canonicalFormula (ρ : Peano.Formula) : Peano.Formula :=
  FOL.existsAt 3 ((FOL.allAt 5
    (((bitFormula (.var 4) (.var 5)).imp
      (ρ.imp (bitFormula (.var 3) (.var 5)))) ⊓
      ((bitFormula (.var 3) (.var 5)).imp ρ))) ⊓
    (ρ.imp (bitFormula (.var 3) (.var 5))))

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl
private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl
private theorem subst_and (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊓ ψ).subst σ = (φ.subst σ) ⊓ (ψ.subst σ) := by
  change (φ.imp ψ.not).not.subst σ = ((φ.subst σ).imp (ψ.subst σ).not).not
  rw [subst_not, subst_imp, subst_not]

/-- PA derives the canonical formula from an arbitrary ρ fresh at names
0,1,2,3. Name 5 may occur in ρ as the outer parameter: under the displayed
universal binder those occurrences are correctly bound. -/
theorem canonical_formula (ρ : Peano.Formula)
    (hρ0 : 0 ∉ ρ.freeVarFinset) (hρ1 : 1 ∉ ρ.freeVarFinset)
    (hρ2 : 2 ∉ ρ.freeVarFinset) (hρ3 : 3 ∉ ρ.freeVarFinset) :
    FormulaProves (canonicalFormula ρ) := by
  let ψ := normalized ρ
  let A := bitFormula (.var 4) (.var 1)
  let B := bitFormula (.var 3) (.var 1)
  let D := (A.imp (ψ.imp B)) ⊓ (B.imp ψ)
  let Q := FOL.allAt 5 (((bitFormula (.var 4) (.var 5)).imp
    (ρ.imp (bitFormula (.var 3) (.var 5)))) ⊓
    ((bitFormula (.var 3) (.var 5)).imp ρ))
  let O := ρ.imp (bitFormula (.var 3) (.var 5))
  let T := canonicalFormula ρ
  have hf := normalized_invariant_fresh ρ hρ0 hρ2 hρ3
  have hψ5 : 5 ∉ ψ.freeVarFinset := normalized_outer_fresh ρ
  have hD5 : 5 ∉ D.freeVarFinset := by
    have hA : 5 ∉ A.freeVarFinset := by decide
    have hB : 5 ∉ B.freeVarFinset := by decide
    change 5 ∉ ((A.imp (ψ.imp B)).imp (B.imp ψ).not).not.freeVarFinset
    simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hA, hB, hψ5]
  have hsyntax : FOL.substAt D 1 (.var 5) =
      (((bitFormula (.var 4) (.var 5)).imp
        (ρ.imp (bitFormula (.var 3) (.var 5)))) ⊓
        ((bitFormula (.var 3) (.var 5)).imp ρ)) := by
    have hround : ψ.subst (fun y => if y = 1 then (.var 5 : Peano.Term) else .var y) = ρ :=
      normalized_roundtrip ρ hρ1
    simp [FOL.substAt, D, A, B, subst_and, subst_imp, bitFormula_subst,
      FirstOrder.Language.Term.subst, hround]
  have hquant : FormulaProves ((quantifiedGoal ψ).imp Q) := by
    have h := PeanoAX8AllAlpha.all_alpha_forward D 1 5 (by decide) hD5
    rw [hsyntax] at h
    simpa only [quantifiedGoal, input, output, idx, D, A, B, Q] using h
  have houter : outerGoal ψ = O := by
    simp only [outerGoal, outer, output, O, ψ, normalized_roundtrip ρ hρ1]
  have hbody : FormulaProves ((quantifiedGoal ψ ⊓ outerGoal ψ).imp T) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    let H := quantifiedGoal ψ ⊓ outerGoal ψ
    have hh : FOL.Context Peano.Axiom [H] H := .head [] _
    have hq : FOL.Context Peano.Axiom [H] Q := .mp (.closed hquant) (FOL.Context.conjunctionLeft hh)
    have ho : FOL.Context Peano.Axiom [H] O := by
      rw [← houter]
      exact FOL.Context.conjunctionRight hh
    have hc : FOL.Context Peano.Axiom [H] (Q ⊓ O) := FOL.Context.conjunctionIntro hq ho
    have hi : FormulaProves ((Q ⊓ O).imp T) := by
      simpa only [T, canonicalFormula, Q, O, SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom) (Q ⊓ O) 3 (.var 3))
    exact .mp (.closed hi) hc
  have hT3 : 3 ∉ T.freeVarFinset := by
    simp [T, canonicalFormula, FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]
  have h := PeanoBitPositionReduction.exists_elim 3 hT3 hbody
  exact .mp (by simpa only [selectedConsequences] using h)
    (PeanoAX8CanonicalClosed.canonical_consequences ψ hf.1 hf.2.1 hf.2.2)

end PASoundness.PeanoAX8CanonicalFormula

#print axioms PASoundness.PeanoAX8CanonicalFormula.canonical_formula
