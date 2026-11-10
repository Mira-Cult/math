import PASoundness.PAtoCompactInductionPredicateAlignment

/-! Finite K alignment between the named induction predicate at a selected
label and the body of the actual translated PA universal. This is an
object-level proof constructor; it does not establish the base or step, or
instantiate the induction theorem's name and selector obligations. -/
namespace PASoundness.PAtoCompactInductionConclusionBody
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactDirectGeneralization
open PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactScopedBindVariable PASoundness.PAtoCompactInductionPredicateAlignment
open PASoundness.PAtoCompactVacuousQuantifierFree

/-- At any lower label a, the induction predicate opened at t and then
replaced at a is K-equivalent to the translated universal body at a.
The target label may already occur free in the source formula. -/
noncomputable def conclusion_body_alignment (φ : Peano.Formula) (x t a : Nat)
    (htop : topName x φ < t) (ha : a < t) :
    KBoth (replace t a (scopeAt φ x t)) (scopeAt φ x a) := by
  have h1 := named_predicate_alignment φ x t a htop ha
  have h2 := formula_bind_variable φ x a
  exact ⟨compose h1.1 h2.1, compose h2.2 h1.2⟩

theorem conclusion_body_forward_certificate (φ : Peano.Formula) (x t a : Nat)
    (htop : topName x φ < t) (ha : a < t) :
    theoremCode (certificate (conclusion_body_alignment φ x t a htop ha).1) =
      imp (replace t a (scopeAt φ x t)).encode (scopeAt φ x a).encode :=
  certificate_correct _

end PASoundness.PAtoCompactInductionConclusionBody

#print axioms PASoundness.PAtoCompactInductionConclusionBody.conclusion_body_alignment
#print axioms PASoundness.PAtoCompactInductionConclusionBody.conclusion_body_forward_certificate
