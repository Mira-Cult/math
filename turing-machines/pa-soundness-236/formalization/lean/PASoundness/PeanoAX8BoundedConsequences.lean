import PASoundness.PeanoAX8SelectorCombine
import PASoundness.PeanoAX8SelectorBound
import PASoundness.PeanoComprehensionBound

/-! Eliminate the explicit selector-bound premise for the fixed-name,
non-alias AX8-shaped consequences, conditional on the full invariant family.
Literal decoded-variable alignment and the invariant successor remain separate. -/
namespace PASoundness.PeanoAX8BoundedConsequences
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoFiniteComprehensionBase PeanoAX8SelectorLogic
open PeanoAX8SelectorExtraction PeanoAX8SelectorCombine

def bounds : Peano.Formula :=
  (less (.var 4) (.var 0)) ⊓ (less (.var 5) (.var 0))

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl
private theorem subst_and (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊓ ψ).subst σ = (φ.subst σ) ⊓ (ψ.subst σ) := by
  change (φ.imp ψ.not).not.subst σ = ((φ.subst σ).imp (ψ.subst σ).not).not
  rw [subst_not, show (φ.imp ψ.not).subst σ = (φ.subst σ).imp (ψ.not.subst σ) from rfl, subst_not]

/-- PA supplies a common strict bound on the input and the outer position. -/
theorem exists_bounds : FormulaProves (FOL.existsAt 0 bounds) := by
  let w : Peano.Term := add (.var 4) (succ (.var 5))
  have h : FormulaProves
      ((less (.var 4) w) ⊓ (less (.var 5) w)) := by
    exact FOL.Context.closeEmpty (FOL.Context.conjunctionIntro
      (.closed (PeanoComprehensionBound.code_below_bound (.var 4) (.var 5)))
      (.closed (PeanoComprehensionBound.position_below_bound (.var 4) (.var 5))))
  have hsub : FOL.substAt bounds 0 w =
      ((less (.var 4) w) ⊓ (less (.var 5) w)) := by
    simp [bounds, FOL.substAt, subst_and,
      CompactArithmetic.less_subst, w,
      FirstOrder.Language.Term.subst]
  have hi := FOL.Derivation.existsIntro (A := Peano.Axiom) bounds 0 w
  rw [hsub] at hi
  exact .mp hi h

private theorem substituted_fresh (ψ : Peano.Formula)
    (hψ0 : 0 ∉ ψ.freeVarFinset) : 0 ∉ (FOL.substAt ψ 1 (.var 5)).freeVarFinset := by
  unfold FOL.substAt
  rw [SyntaxTransport.formula_subst_freeVars]
  rintro ⟨j, hj, hz⟩
  by_cases h : j = 1
  · subst j
    simp [FirstOrder.Language.Term.varFinset] at hz
  · have hj0 : j = 0 := by
      have hz' : 0 = j := by simpa [h, FirstOrder.Language.Term.varFinset] using hz
      exact hz'.symm
    subst j
    exact hψ0 hj

private theorem consequence_fresh (ψ : Peano.Formula)
    (hψ0 : 0 ∉ ψ.freeVarFinset) : 0 ∉ (selectedConsequences ψ).freeVarFinset := by
  have hb : 0 ∉ (bitFormula output idx).freeVarFinset := by decide
  have ha : 0 ∉ (bitFormula input idx).freeVarFinset := by decide
  have he : 0 ∉ (bitFormula output outer).freeVarFinset := by decide
  have hs := substituted_fresh ψ hψ0
  have hqb : 0 ∉ (((bitFormula input idx).imp (ψ.imp (bitFormula output idx))) ⊓
      ((bitFormula output idx).imp ψ)).freeVarFinset := by
    change 0 ∉ (((bitFormula input idx).imp (ψ.imp (bitFormula output idx))).imp
      ((bitFormula output idx).imp ψ).not).not.freeVarFinset
    simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hψ0, hb, ha]
  have hq : 0 ∉ (quantifiedGoal ψ).freeVarFinset := by
    unfold quantifiedGoal
    rw [SyntaxTransport.allAt_freeVars]
    simp [hqb]
  have ho : 0 ∉ (outerGoal ψ).freeVarFinset := by
    change 0 ∉ ((FOL.substAt ψ 1 (.var 5)).imp (bitFormula output outer)).freeVarFinset
    simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hs, he]
  have hc : 0 ∉ (quantifiedGoal ψ ⊓ outerGoal ψ).freeVarFinset := by
    change 0 ∉ ((quantifiedGoal ψ).imp (outerGoal ψ).not).not.freeVarFinset
    simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hq, ho]
  simp [selectedConsequences, FOL.existsAt, SyntaxTransport.allAt_freeVars,
    FirstOrder.Language.BoundedFormula.not,
    FirstOrder.Language.BoundedFormula.freeVarFinset, hc]

/-- For any relation fresh in the state names, a PA proof of its full
bounded-invariant family yields a common code with both fixed-name
AX8-shaped conclusions. The full-invariant family remains an explicit
object-level premise. -/
theorem consequences_of_invariant_family (ψ : Peano.Formula)
    (hψ0 : 0 ∉ ψ.freeVarFinset) (hψ2 : 2 ∉ ψ.freeVarFinset)
    (hψ3 : 3 ∉ ψ.freeVarFinset) : FormulaProves
      ((FOL.allAt 0 (invariant (selected ψ) (.var 0))).imp
        (selectedConsequences ψ)) := by
  let H := FOL.allAt 0 (invariant (selected ψ) (.var 0))
  let T := selectedConsequences ψ
  have hbody : FormulaProves (bounds.imp (H.imp T)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [H, bounds]
    have hb : FOL.Context Peano.Axiom Γ bounds := .hypothesis (by simp [Γ])
    have hh : FOL.Context Peano.Axiom Γ H := FOL.Context.head _ _
    have hi : FOL.Context Peano.Axiom Γ (invariant (selected ψ) (.var 0)) :=
      FOL.Context.allSelf hh
    have hl := FOL.Context.conjunctionLeft hb
    have hr := FOL.Context.conjunctionRight hb
    have hs : FOL.Context Peano.Axiom Γ (selectorBound (selected ψ)) := by
      have q := PeanoAX8SelectorBound.selector_bounded ψ
      exact .mp (.mp (.closed (by simpa [selectorBound, selected, input, idx, outer,
        PeanoAX8SelectorBound.selector] using q)) hl) hr
    exact .mp (.mp (.closed (invariant_to_consequences ψ hψ2 hψ3)) hi) hs
  have hf : 0 ∉ (H.imp T).freeVarFinset := by
    have ht := consequence_fresh ψ hψ0
    simp [H, T, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.freeVarFinset, ht]
  have he := PeanoBitPositionReduction.exists_elim 0 hf hbody
  exact .mp he exists_bounds

end PASoundness.PeanoAX8BoundedConsequences

#print axioms PASoundness.PeanoAX8BoundedConsequences.exists_bounds
#print axioms PASoundness.PeanoAX8BoundedConsequences.consequences_of_invariant_family
