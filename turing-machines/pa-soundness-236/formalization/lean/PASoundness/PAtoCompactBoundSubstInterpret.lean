import PASoundness.SyntaxTransport
import PASoundness.PAtoCompactScopedAlphaInvariant

/-! Capture-avoiding interpretation of substitutions inside a bounded PA
scope. Free variables and active bound levels remain distinct until the
substitution has been applied; their interpreted names may alias. -/
namespace PASoundness.PAtoCompactBoundSubstInterpret

open FirstOrder FirstOrder.Language
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedAlphaInvariant

/-- Apply the free substitution first, then interpret the active bound levels.
No injectivity or distinctness assumption is imposed on `bound`. -/
theorem interpret_subst {n : Nat}
    (t : Peano.language.Term (Nat ⊕ Fin n)) (σ : Nat → Peano.Term)
    (bound : Fin n → Nat) :
    (t.subst (PASoundness.SyntaxTransport.liftSub n σ)).relabel (Sum.elim id bound) =
      t.subst (Sum.elim σ (Term.var ∘ bound)) := by
  rw [PASoundness.SyntaxTransport.term_subst_relabel]
  congr 1
  funext a
  cases a with
  | inl a =>
      change ((σ a).relabel Sum.inl).relabel (Sum.elim id bound) = σ a
      rw [Term.relabel_relabel]
      exact Term.relabel_id _
  | inr i => rfl

/-- The same identity as an equality of the generated term graphs. -/
theorem graph_interpret_subst {n : Nat}
    (t : Peano.language.Term (Nat ⊕ Fin n)) (σ : Nat → Peano.Term)
    (bound : Fin n → Nat) (out base : Nat) :
    termGraph (Sum.elim id bound) (t.subst (PASoundness.SyntaxTransport.liftSub n σ)) out base =
      termGraph id (t.subst (Sum.elim σ (Term.var ∘ bound))) out base := by
  have h := termGraph_relabel (t.subst (PASoundness.SyntaxTransport.liftSub n σ))
    (Sum.elim id bound) id out base
  simp only [Function.id_comp] at h
  rw [← h, interpret_subst]

end PASoundness.PAtoCompactBoundSubstInterpret

#print axioms PASoundness.PAtoCompactBoundSubstInterpret.interpret_subst
#print axioms PASoundness.PAtoCompactBoundSubstInterpret.graph_interpret_subst
