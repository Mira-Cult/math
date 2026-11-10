import PASoundness.PAtoCompactScopedSuccSubstFull
import PASoundness.PAtoCompactScopedSuccessorEqualityFull

/-! Finite K formula alignment under a retained successor graph. -/
namespace PASoundness.PAtoCompactScopedSuccessorComplete

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedLogicalCongruence
open PASoundness.PAtoCompactScopedSuccSubstFull
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactUnaryTermTransport
open PASoundness.PAtoCompactTermSubstSuccessorInduction PASoundness.PAtoCompactSuccSubstSyntax
open PASoundness.PAtoCompactScopedSuccessorEqualityFull

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Equality-node proofs for arbitrary bound maps, including aliases. -/
abbrev AtomHandler (H : Formula) (σ τ : Nat → Peano.Term) :=
  ∀ (n : Nat) (s t : Peano.language.Term (Nat ⊕ Fin n)) (bound : Fin n → Nat),
    GuardedBoth H
      (scopedFormula n ((.equal s t : Peano.language.BoundedFormula Nat n).subst σ) bound)
      (scopedFormula n ((.equal s t : Peano.language.BoundedFormula Nat n).subst τ) bound)

/-- Restrict the uniform atom handler to precisely the actual equality nodes
of the source formula. -/
noncomputable def leaves_of_handler (H : Formula) (σ τ : Nat → Peano.Term)
    (atom : AtomHandler H σ τ) {n : Nat} (φ : Peano.language.BoundedFormula Nat n) :
    ScopedLeaves H σ τ φ := by
  induction φ with
  | falsum => exact .falsum
  | @equal n s t => exact .equal s t (atom n s t)
  | rel r ts => exact nomatch r
  | imp a b ia ib => exact .imp ia ib
  | all body ih => exact .all ih

/-- Generic bounded formula alignment conditional on the uniform atom proof. -/
noncomputable def scoped_of_handler (H : Formula) (σ τ : Nat → Peano.Term)
    (atom : AtomHandler H σ τ) {n : Nat} (φ : Peano.language.BoundedFormula Nat n)
    (bound : Fin n → Nat) :
    GuardedBoth H (scopedFormula n (φ.subst σ) bound)
      (scopedFormula n (φ.subst τ) bound) :=
  scoped_substitution H σ τ (leaves_of_handler H σ τ atom φ) bound

/-- Given a graph witness for `S u`, source substitutions by its value name
and by `S u` agree at every formula depth, with no restrictions on aliases in
the active-name environment. Candidate proofs for the variables of `u` are
explicit finite K inputs. -/
noncomputable def scoped_successor_substitution
    (g : Formula) (u : Peano.Term) (hu : UnaryTerm u) (x q d : Nat)
    (hqd : q < d) (hud : ∀ a ∈ u.varFinset, a < d)
    (hdom : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    {n : Nat} (φ : Peano.language.BoundedFormula Nat n) (bound : Fin n → Nat) :
    GuardedBoth (retained g u q d)
      (scopedFormula n (φ.subst (singleSubst x (.var q))) bound)
      (scopedFormula n (φ.subst (singleSubst x (succTerm u))) bound) := by
  apply scoped_of_handler (retained g u q d) (singleSubst x (.var q))
    (singleSubst x (succTerm u)) _ φ bound
  intro n s t bound
  exact scoped_successor_equal g u hu x q d hqd hud hdom s t bound

/-- Top-level PA formulas inherit the same two finite K implications. -/
noncomputable def formula_successor_substitution
    (g : Formula) (u : Peano.Term) (hu : UnaryTerm u) (x q d : Nat)
    (hqd : q < d) (hud : ∀ a ∈ u.varFinset, a < d)
    (hdom : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (φ : Peano.Formula) :
    GuardedBoth (retained g u q d)
      (formula (FOL.substAt φ x (.var q))) (formula (FOL.substAt φ x (succTerm u))) := by
  change GuardedBoth (retained g u q d)
    (scopedFormula 0 (φ.subst (singleSubst x (.var q))) Fin.elim0)
    (scopedFormula 0 (φ.subst (singleSubst x (succTerm u))) Fin.elim0)
  exact scoped_successor_substitution g u hu x q d hqd hud hdom φ Fin.elim0

theorem formula_successor_forward_certificate
    (g : Formula) (u : Peano.Term) (hu : UnaryTerm u) (x q d : Nat)
    (hqd : q < d) (hud : ∀ a ∈ u.varFinset, a < d)
    (hdom : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (φ : Peano.Formula) :
    theoremCode (certificate ((formula_successor_substitution g u hu x q d hqd hud hdom φ).1)) =
      imp (retained g u q d).encode
        (imp (formula (FOL.substAt φ x (.var q))).encode
          (formula (FOL.substAt φ x (succTerm u))).encode) := certificate_correct _

theorem formula_successor_backward_certificate
    (g : Formula) (u : Peano.Term) (hu : UnaryTerm u) (x q d : Nat)
    (hqd : q < d) (hud : ∀ a ∈ u.varFinset, a < d)
    (hdom : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (φ : Peano.Formula) :
    theoremCode (certificate ((formula_successor_substitution g u hu x q d hqd hud hdom φ).2)) =
      imp (retained g u q d).encode
        (imp (formula (FOL.substAt φ x (succTerm u))).encode
          (formula (FOL.substAt φ x (.var q))).encode) := certificate_correct _

end PASoundness.PAtoCompactScopedSuccessorComplete

#print axioms PASoundness.PAtoCompactScopedSuccessorComplete.leaves_of_handler
#print axioms PASoundness.PAtoCompactScopedSuccessorComplete.scoped_of_handler
#print axioms PASoundness.PAtoCompactScopedSuccessorComplete.scoped_successor_substitution
#print axioms PASoundness.PAtoCompactScopedSuccessorComplete.formula_successor_substitution
#print axioms PASoundness.PAtoCompactScopedSuccessorComplete.formula_successor_forward_certificate
#print axioms PASoundness.PAtoCompactScopedSuccessorComplete.formula_successor_backward_certificate
