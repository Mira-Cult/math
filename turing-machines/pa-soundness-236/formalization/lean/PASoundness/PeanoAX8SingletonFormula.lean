import PASoundness.PeanoAX8SingletonCanonical
import PASoundness.PeanoAX8PredicateNormalize
import PASoundness.PeanoAX8AllAlpha

/-! Exact canonical alias-reduced formula for a fresh arbitrary predicate.
It does not yet identify arbitrary literal AX8 names or decoded predicates. -/
namespace PASoundness.PeanoAX8SingletonFormula
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoAX8SingletonCombine PeanoAX8PredicateNormalize

/-- Both alias-reduced obligations use one existential code. The outer
occurrence of name 5 is outside the universal binder. -/
def canonicalReduced (ρ : Peano.Formula) : Peano.Formula :=
  FOL.existsAt 3 ((FOL.allAt 5 ((bitFormula (.var 3) (.var 5)).imp ρ)) ⊓
    (ρ.imp (bitFormula (.var 3) (.var 5))))

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl

/-- PA derives the exact canonical singleton formula for any ρ fresh at the
displayed state and temporary names. ρ may contain free name 5. -/
theorem canonical_reduced (ρ : Peano.Formula)
    (hρ0 : 0 ∉ ρ.freeVarFinset) (hρ1 : 1 ∉ ρ.freeVarFinset)
    (hρ2 : 2 ∉ ρ.freeVarFinset) (hρ3 : 3 ∉ ρ.freeVarFinset) :
    FormulaProves (canonicalReduced ρ) := by
  let ψ := normalized ρ
  let B := bitFormula (.var 3) (.var 1)
  let D := B.imp ψ
  let Q := FOL.allAt 5 ((bitFormula (.var 3) (.var 5)).imp ρ)
  let O := ρ.imp (bitFormula (.var 3) (.var 5))
  let T := canonicalReduced ρ
  have hf := normalized_invariant_fresh ρ hρ0 hρ2 hρ3
  have hψ5 : 5 ∉ ψ.freeVarFinset := normalized_outer_fresh ρ
  have hD5 : 5 ∉ D.freeVarFinset := by
    have hB : 5 ∉ B.freeVarFinset := by decide
    simp [D, FirstOrder.Language.BoundedFormula.freeVarFinset, hB, hψ5]
  have hsyntax : FOL.substAt D 1 (.var 5) =
      ((bitFormula (.var 3) (.var 5)).imp ρ) := by
    have hround : ψ.subst (fun y => if y = 1 then (.var 5 : Peano.Term) else .var y) = ρ :=
      normalized_roundtrip ρ hρ1
    simp [FOL.substAt, D, B, subst_imp, bitFormula_subst, FirstOrder.Language.Term.subst, hround]
  have hquant : FormulaProves ((FOL.allAt 1 D).imp Q) := by
    have h := PeanoAX8AllAlpha.all_alpha_forward D 1 5 (by decide) hD5
    rw [hsyntax] at h
    exact h
  have houter : (FOL.substAt ψ 1 (.var 5)).imp (bitFormula (.var 3) (.var 5)) = O := by
    simp only [O, ψ, normalized_roundtrip ρ hρ1]
  have hbody : FormulaProves ((aliasConsequences ψ).imp T) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    let H := aliasConsequences ψ
    have hh : FOL.Context Peano.Axiom [H] H := .head [] _
    have hq : FOL.Context Peano.Axiom [H] Q :=
      .mp (.closed hquant) (FOL.Context.conjunctionLeft hh)
    have ho : FOL.Context Peano.Axiom [H] O := by
      rw [← houter]
      exact FOL.Context.conjunctionRight hh
    have hc : FOL.Context Peano.Axiom [H] (Q ⊓ O) := FOL.Context.conjunctionIntro hq ho
    have hi : FormulaProves ((Q ⊓ O).imp T) := by
      simpa only [T, canonicalReduced, Q, O, SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom) (Q ⊓ O) 3 (.var 3))
    exact .mp (.closed hi) hc
  have hT3 : 3 ∉ T.freeVarFinset := by
    simp [T, canonicalReduced, FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]
  have h := PeanoBitPositionReduction.exists_elim 3 hT3 hbody
  exact .mp h (PeanoAX8SingletonCanonical.canonical_singleton ψ hf.1 hf.2.1 hf.2.2)

end PASoundness.PeanoAX8SingletonFormula

#print axioms PASoundness.PeanoAX8SingletonFormula.canonical_reduced
