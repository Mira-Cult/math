import PASoundness.PeanoAX8SelectorLogic
import PASoundness.PeanoBetaCRTAlpha

/-! Capture-safe renaming of the selected code's existential name. -/
namespace PASoundness.PeanoAX8OutputAlpha
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoAX8SelectorLogic

/-- PA can rename an existential output from canonical name 3 to a distinct
name c fresh for its body. This is a derivation transformation, not AX8. -/
theorem output_alpha (φ : Peano.Formula) (c : Nat) (h3c : 3 ≠ c)
    (hc : c ∉ φ.freeVarFinset) : FormulaProves
    ((FOL.existsAt 3 φ).imp (FOL.existsAt c (FOL.substAt φ 3 (.var c)))) :=
  PeanoBetaCRTAlpha.exists_alpha_forward φ 3 c h3c hc

private theorem outer_subst_fresh (ψ : Peano.Formula) (c : Nat)
    (hc : c ∉ ψ.freeVarFinset) (hc5 : c ≠ 5) :
    c ∉ (FOL.substAt ψ 1 (.var 5)).freeVarFinset := by
  unfold FOL.substAt
  rw [SyntaxTransport.formula_subst_freeVars]
  rintro ⟨x,hx,h⟩
  by_cases hx1 : x = 1
  · subst x
    simp [FirstOrder.Language.Term.varFinset, hc5] at h
  · have he : c = x := by simpa [hx1, FirstOrder.Language.Term.varFinset] using h
    subst x
    exact hc hx

private theorem inf_free (φ ψ : Peano.Formula) :
    (φ ⊓ ψ).freeVarFinset = φ.freeVarFinset ∪ ψ.freeVarFinset := by
  change ((φ.imp ψ.not).not).freeVarFinset = _
  simp [FirstOrder.Language.BoundedFormula.freeVarFinset]

/-- A sufficient canonical-name freshness condition for the combined goal.
The explicit numeric inequalities must be supplied by the caller's name
alignment; this theorem does not infer them from literal AX8 guards. -/
theorem canonical_body_fresh (ψ : Peano.Formula) (c : Nat)
    (hc : c ∉ ψ.freeVarFinset)
    (hc3 : c ≠ 3) (hc4 : c ≠ 4) (hc5 : c ≠ 5) :
    c ∉ (quantifiedGoal ψ ⊓ outerGoal ψ).freeVarFinset := by
  have hs := outer_subst_fresh ψ c hc hc5
  simp [quantifiedGoal, outerGoal, input, output, idx, outer,
    SyntaxTransport.allAt_freeVars, inf_free,
    FirstOrder.Language.BoundedFormula.freeVarFinset, bitFormula_freeVars,
    FirstOrder.Language.Term.varFinset, hc, hs, hc3, hc4, hc5]

end PASoundness.PeanoAX8OutputAlpha

#print axioms PASoundness.PeanoAX8OutputAlpha.output_alpha
#print axioms PASoundness.PeanoAX8OutputAlpha.canonical_body_fresh
