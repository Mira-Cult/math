import PASoundness.PAtoCompactBoundSubstInterpret
import PASoundness.PAtoCompactVacuousEqualityAlignment

/-! Syntactic alignment of a substituted bounded equality with its interpreted
named equality frame. Active bound labels may coincide with one another and
with free labels; there is no injectivity hypothesis. -/
namespace PASoundness.PAtoCompactScopedSubstitutedEqualityShape
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactBoundSubstInterpret PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.SyntaxTransport

/-- Interpretation commutes with capture-avoiding source substitution and
uses the actual allocator of the substituted equality. -/
theorem scoped_substituted_equality_shape {n : Nat}
    (s t : Peano.language.Term (Nat ⊕ Fin n)) (σ : Nat → Peano.Term)
    (bound : Fin n → Nat) :
    scopedFormula n ((.equal s t : Peano.language.BoundedFormula Nat n).subst σ) bound =
      equalityFrame id (s.subst (Sum.elim σ (Term.var ∘ bound)))
        (t.subst (Sum.elim σ (Term.var ∘ bound)))
        (scopeBase ((.equal s t : Peano.language.BoundedFormula Nat n).subst σ) bound) := by
  change scopedFormula n (.equal (s.subst (liftSub n σ)) (t.subst (liftSub n σ))) bound = _
  rw [scoped_equal_frame]
  have h := frame_relabel (s.subst (liftSub n σ)) (t.subst (liftSub n σ)) (Sum.elim id bound) id
    (scopeBase (.equal (s.subst (liftSub n σ)) (t.subst (liftSub n σ))) bound)
  simp only [Function.id_comp] at h
  rw [← h]
  rw [interpret_subst, interpret_subst]
  rfl

end PASoundness.PAtoCompactScopedSubstitutedEqualityShape

#print axioms PASoundness.PAtoCompactScopedSubstitutedEqualityShape.scoped_substituted_equality_shape
