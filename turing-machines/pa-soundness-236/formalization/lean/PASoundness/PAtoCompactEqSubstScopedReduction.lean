import PASoundness.PAtoCompactScopedSuccSubstFull
import PASoundness.PAtoCompactSuccSubstSyntax
import PASoundness.PAtoCompactGuardedBridge

/-! Reduce the guarded PA equality-substitution handler to K proof data for
the actual equality nodes of its source formula. The equality-node family is
an explicit input; this module does not establish it, arbitrary-term graph
functionality, or semantic soundness. -/
namespace PASoundness.PAtoCompactEqSubstScopedReduction

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactScopedSuccSubstFull PASoundness.PAtoCompactSuccSubstSyntax

/-- The literal PA equality-substitution axiom instance. -/
def axiomFormula (φ : Peano.Formula) (x : Nat) (t u : Peano.Term) : Peano.Formula :=
  (t.equal u).imp ((FOL.substAt φ x t).imp (FOL.substAt φ x u))

/-- The exact guard and translated equality retained while traversing the
source formula. -/
def retained (φ : Peano.Formula) (x : Nat) (t u : Peano.Term) : Formula :=
  andF (guardFormula (axiomFormula φ x t u)) (formula (t.equal u))

/-- Explicit finite K alignment proofs for the actual equality leaves, under
every active-name environment, suffice for the guarded equality-substitution
instance. Free names and active bound labels may alias; no injectivity or
candidate-domain premise for active labels is added here. -/
noncomputable def eqSubst_of_scoped_leaves (φ : Peano.Formula) (x : Nat) (t u : Peano.Term)
    (leaves : ScopedLeaves (retained φ x t u) (singleSubst x t) (singleSubst x u) φ) :
    KDerivation (guardedCode (axiomFormula φ x t u)) := by
  have h := (scoped_substitution (retained φ x t u) (singleSubst x t)
    (singleSubst x u) leaves Fin.elim0).1
  change KDerivation (imp (retained φ x t u).encode
    (imp (code (FOL.substAt φ x t)) (code (FOL.substAt φ x u)))) at h
  change KDerivation (imp (guardFormula (axiomFormula φ x t u)).encode
    (imp (code (t.equal u))
      (imp (code (FOL.substAt φ x t)) (code (FOL.substAt φ x u)))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let G := (guardFormula (axiomFormula φ x t u)).encode
  let E := code (t.equal u)
  let P := code (FOL.substAt φ x t)
  let Γ := [P, E, G]
  have hp : Context Γ P := Context.head _ _
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hret : Context Γ (retained φ x t u).encode := by
    have hc := Context.conjunctionIntro hg he
    simpa [retained, code, andF, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg, G, E] using hc
  exact .mp hp (.mp hret (.closed h))

/-- A family of actual-leaf proof data for every PA axiom instance produces
the entire guarded equality-substitution handler. -/
abbrev ScopedLeafFamily :=
  ∀ (φ : Peano.Formula) (x : Nat) (t u : Peano.Term),
    ScopedLeaves (retained φ x t u) (singleSubst x t) (singleSubst x u) φ

noncomputable def eqSubst_handler (leaves : ScopedLeafFamily)
    (φ : Peano.Formula) (x : Nat) (t u : Peano.Term) :
    KDerivation (guardedCode ((t.equal u).imp
      ((FOL.substAt φ x t).imp (FOL.substAt φ x u)))) :=
  eqSubst_of_scoped_leaves φ x t u (leaves φ x t u)

theorem eqSubst_certificate (φ : Peano.Formula) (x : Nat) (t u : Peano.Term)
    (leaves : ScopedLeaves (retained φ x t u) (singleSubst x t) (singleSubst x u) φ) :
    theoremCode (certificate (eqSubst_of_scoped_leaves φ x t u leaves)) =
      guardedCode (axiomFormula φ x t u) := certificate_correct _

end PASoundness.PAtoCompactEqSubstScopedReduction

#print axioms PASoundness.PAtoCompactEqSubstScopedReduction.axiomFormula
#print axioms PASoundness.PAtoCompactEqSubstScopedReduction.retained
#print axioms PASoundness.PAtoCompactEqSubstScopedReduction.eqSubst_of_scoped_leaves
#print axioms PASoundness.PAtoCompactEqSubstScopedReduction.ScopedLeafFamily
#print axioms PASoundness.PAtoCompactEqSubstScopedReduction.eqSubst_handler
#print axioms PASoundness.PAtoCompactEqSubstScopedReduction.eqSubst_certificate
