import PASoundness.PAtoCompactMulReversalTermNaturality
import PASoundness.SyntaxTransport

/-! Capture-safe syntactic naturality of multiplication reversal. These are
identities of PA syntax, not proof translations or multiplication laws. -/

namespace PASoundness.PAtoCompactMulReversalFormulaNaturality

open FirstOrder FirstOrder.Language
open PASoundness.PAtoCompactMulReversalSyntax
open PASoundness.PAtoCompactMulReversalTermNaturality
open PASoundness.SyntaxTransport

/-- Reversal commutes with a relabeling that may bind free variables, at any
scope depth. Existing bound-variable indices are treated by the standard
capture-safe relabeling. -/
theorem reverseBounded_relabel {α β : Type} {k n : Nat}
    (φ : Peano.language.BoundedFormula α n) (r : α → β ⊕ Fin k) :
    reverseBounded (k+n) (φ.relabel r) = (reverseBounded n φ).relabel r := by
  induction φ with
  | falsum => rfl
  | equal t u =>
      change BoundedFormula.equal
        (reverseTerm (t.relabel (BoundedFormula.relabelAux r _)))
        (reverseTerm (u.relabel (BoundedFormula.relabelAux r _))) =
        BoundedFormula.equal
          ((reverseTerm t).relabel (BoundedFormula.relabelAux r _))
          ((reverseTerm u).relabel (BoundedFormula.relabelAux r _))
      rw [reverseTerm_relabel, reverseTerm_relabel]
  | rel r ts => exact nomatch r
  | imp φ ψ ihφ ihψ =>
      simp only [BoundedFormula.relabel_imp, reverseBounded_imp, ihφ, ihψ]
  | all φ ih =>
      simp only [BoundedFormula.relabel_all, reverseBounded_all]
      exact congrArg BoundedFormula.all ih

/-- Lifting a substitution under binders commutes with reversal of its terms. -/
theorem reverse_liftSub {α β : Type} (n : Nat)
    (σ : α → Peano.language.Term β) :
    (fun x => reverseTerm (liftSub n σ x)) =
      liftSub n (fun a => reverseTerm (σ a)) := by
  funext x
  cases x with
  | inl a =>
      simp only [liftSub, Sum.elim_inl, Function.comp_apply, reverseTerm_relabel]
  | inr i => rfl

/-- Reversal commutes with the standard capture-avoiding substitution after
reversing every substituted term. -/
theorem reverseBounded_subst {α β : Type} {n : Nat}
    (φ : Peano.language.BoundedFormula α n) (σ : α → Peano.language.Term β) :
    reverseBounded n (φ.subst σ) = (reverseBounded n φ).subst (fun a => reverseTerm (σ a)) := by
  induction φ with
  | falsum => rfl
  | equal t u =>
      change BoundedFormula.equal (reverseTerm (t.subst (liftSub _ σ)))
          (reverseTerm (u.subst (liftSub _ σ))) =
        BoundedFormula.equal ((reverseTerm t).subst (liftSub _ (fun a => reverseTerm (σ a))))
          ((reverseTerm u).subst (liftSub _ (fun a => reverseTerm (σ a))))
      simp only [reverseTerm_subst, reverse_liftSub]
  | rel r ts => exact nomatch r
  | imp φ ψ ihφ ihψ =>
      change BoundedFormula.imp (reverseBounded _ (φ.subst σ)) (reverseBounded _ (ψ.subst σ)) =
        BoundedFormula.imp ((reverseBounded _ φ).subst _) ((reverseBounded _ ψ).subst _)
      rw [ihφ, ihψ]
  | all φ ih =>
      change BoundedFormula.all (reverseBounded _ (φ.subst σ)) =
        BoundedFormula.all ((reverseBounded _ φ).subst _)
      rw [ih]

/-- The reversal does not change which free variables occur. -/
theorem reverseBounded_freeVarFinset {α : Type} [DecidableEq α] {n : Nat}
    (φ : Peano.language.BoundedFormula α n) :
    (reverseBounded n φ).freeVarFinset = φ.freeVarFinset := by
  induction φ with
  | falsum => rfl
  | equal t u =>
      simp only [reverseBounded_equal, BoundedFormula.freeVarFinset, reverseTerm_varFinsetLeft]
  | rel r ts => exact nomatch r
  | imp φ ψ ihφ ihψ =>
      simp only [reverseBounded_imp, BoundedFormula.freeVarFinset, ihφ, ihψ]
  | all φ ih =>
      simpa only [reverseBounded_all, BoundedFormula.freeVarFinset] using ih

/-- In particular, named universal binding is preserved. -/
theorem reverse_allAt (x : Nat) (φ : Peano.Formula) :
    reverseBounded 0 (FOL.allAt x φ) = FOL.allAt x (reverseBounded 0 φ) := by
  unfold FOL.allAt
  rw [reverseBounded_all]
  congr 1
  exact reverseBounded_relabel φ _

/-- Named capture-avoiding substitution is preserved with the substituted
term reversed. -/
theorem reverse_substAt (φ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    reverseBounded 0 (FOL.substAt φ x t) = FOL.substAt (reverseBounded 0 φ) x (reverseTerm t) := by
  unfold FOL.substAt
  rw [reverseBounded_subst]
  congr 1
  funext y
  by_cases h : y = x <;> simp [h]

/-- Literal formula equality reverses both of its term operands; the two sides
of the equality itself retain their order. -/
theorem reverse_term_equal {α : Type} (t u : Peano.language.Term α) :
    reverseBounded 0 (t.equal u) = (reverseTerm t).equal (reverseTerm u) := by
  simp only [Term.equal, Term.bdEqual, reverseBounded_equal, reverseTerm_relabel]

end PASoundness.PAtoCompactMulReversalFormulaNaturality

#print axioms PASoundness.PAtoCompactMulReversalFormulaNaturality.reverseBounded_relabel
#print axioms PASoundness.PAtoCompactMulReversalFormulaNaturality.reverse_liftSub
#print axioms PASoundness.PAtoCompactMulReversalFormulaNaturality.reverseBounded_subst
#print axioms PASoundness.PAtoCompactMulReversalFormulaNaturality.reverseBounded_freeVarFinset
#print axioms PASoundness.PAtoCompactMulReversalFormulaNaturality.reverse_allAt
#print axioms PASoundness.PAtoCompactMulReversalFormulaNaturality.reverse_substAt
#print axioms PASoundness.PAtoCompactMulReversalFormulaNaturality.reverse_term_equal
