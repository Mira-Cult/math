import PASoundness.PeanoAX8BoundedConsequences
import PASoundness.PeanoFiniteComprehensionClosed

/-! Closed fixed-name AX8-shaped selector consequences in PA.
Transport to arbitrary literal AX8 names and its alias case are separate. -/
namespace PASoundness.PeanoAX8CanonicalClosed
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoFiniteComprehensionBase PeanoAX8SelectorLogic PeanoAX8SelectorCombine

/-- Given the explicit state-name freshness conditions on ψ, PA constructs
one code satisfying the fixed-name quantified implications and the separate
outer-position implication. This is not the arbitrary-name AX8 formula. -/
theorem canonical_consequences (ψ : Peano.Formula)
    (hψ0 : 0 ∉ ψ.freeVarFinset) (hψ2 : 2 ∉ ψ.freeVarFinset)
    (hψ3 : 3 ∉ ψ.freeVarFinset) :
    FormulaProves (selectedConsequences ψ) := by
  have h0 : 0 ∉ (selected ψ).freeVarFinset := by
    have hor : 0 ∉ (bitFormula input idx ⊔ idx.equal outer).freeVarFinset := by decide
    change 0 ∉ (((bitFormula input idx ⊔ idx.equal outer).imp ψ.not).not).freeVarFinset
    simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hor, hψ0]
  have h2 : 2 ∉ (selected ψ).freeVarFinset := by
    have hor : 2 ∉ (bitFormula input idx ⊔ idx.equal outer).freeVarFinset := by decide
    change 2 ∉ (((bitFormula input idx ⊔ idx.equal outer).imp ψ.not).not).freeVarFinset
    simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hor, hψ2]
  have h3 : 3 ∉ (selected ψ).freeVarFinset := by
    have hor : 3 ∉ (bitFormula input idx ⊔ idx.equal outer).freeVarFinset := by decide
    change 3 ∉ (((bitFormula input idx ⊔ idx.equal outer).imp ψ.not).not).freeVarFinset
    simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hor, hψ3]
  exact .mp (PeanoAX8BoundedConsequences.consequences_of_invariant_family ψ hψ0 hψ2 hψ3)
    (PeanoFiniteComprehensionClosed.selector_total (selected ψ) h0 h2 h3)

end PASoundness.PeanoAX8CanonicalClosed

#print axioms PASoundness.PeanoAX8CanonicalClosed.canonical_consequences
