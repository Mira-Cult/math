import PASoundness.PAtoCompactGuardedPropositional
import PASoundness.PAtoCompactGuardedGeneralizationAlignment
import PASoundness.PAtoCompactGuardedAllImpAlignment
import PASoundness.CompactDerivations

/-! Finite K proof data for the guarded PA universal-distribution axiom,
using capture-safe alignment to a common freshly chosen binder. -/
namespace PASoundness.PAtoCompactGuardedAllImp

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedPropositional
open PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactGuardedAllImpAlignment

/-- K proves distribution for three universals sharing a binder and domain. -/
def guardedAllDistribution (z d a b : Nat) :
    KDerivation (imp (allCode z (imp d (imp a b)))
      (imp (allCode z (imp d a)) (allCode z (imp d b)))) :=
  compose (allCongr z (CompactHilbertBasis.distribution d a b))
    (allDistribution z (imp d a) (imp d b))

/-- The actual translated source body, opened at a supplied common name. -/
def bodyAt (x : Nat) (φ : Peano.Formula) (z : Nat) : Formula :=
  scopedFormula 1 (allAtBody x φ) (Fin.snoc Fin.elim0 z)

/-- The candidate-guarded universal using that common name. -/
def commonAll (x : Nat) (φ : Peano.Formula) (z : Nat) : Nat :=
  allCode z (imp (domainAt (z+1) z).encode (bodyAt x φ z).encode)

theorem bodyAt_imp (x : Nat) (φ ψ : Peano.Formula) (z : Nat) :
    bodyAt x (φ.imp ψ) z = .imp (bodyAt x φ z) (bodyAt x ψ z) := by
  simp [bodyAt, allAtBody, BoundedFormula.relabel_imp, scopedFormula]

/-- Given the three actual common-binder K implications at a chosen name,
construct the guarded all-implication logical axiom. -/
def translated_allImp_at (φ ψ : Peano.Formula) (x z : Nat)
    (hi : KDerivation (imp (code (FOL.allAt x (φ.imp ψ))) (commonAll x (φ.imp ψ) z)))
    (hφ : KDerivation (imp (code (FOL.allAt x φ)) (commonAll x φ z)))
    (hψ : KDerivation (imp (commonAll x ψ z) (code (FOL.allAt x ψ)))) :
    KDerivation (guardedCode ((FOL.allAt x (φ.imp ψ)).imp
      ((FOL.allAt x φ).imp (FOL.allAt x ψ)))) := by
  apply guardedOfUnconditional
  simp only [code_imp]
  have hdist := guardedAllDistribution z (domainAt (z+1) z).encode
    (bodyAt x φ z).encode (bodyAt x ψ z).encode
  have hc : KDerivation (imp (commonAll x (φ.imp ψ) z)
      (imp (commonAll x φ z) (commonAll x ψ z))) := by
    simpa [commonAll, bodyAt_imp, Formula.encode] using hdist
  exact compose hi (compose hc (implicationCongr hφ hψ))

/-- A bound for both the generated binder and all names in its child. -/
def universalCeiling (φ : Peano.Formula) (x : Nat) : Nat :=
  max (topName x φ) ((originalChild φ x).names.sup id)

/-- One name fresh for all three universals appearing in the PA axiom. -/
def jointName (φ ψ : Peano.Formula) (x : Nat) : Nat :=
  max (universalCeiling (φ.imp ψ) x)
    (max (universalCeiling φ x) (universalCeiling ψ x)) + 1

theorem ceiling_top (φ : Peano.Formula) (x : Nat) :
    topName x φ ≤ universalCeiling φ x := by
  unfold universalCeiling
  omega

theorem ceiling_child (φ : Peano.Formula) (x y : Nat)
    (hy : y ∈ (originalChild φ x).names) : y ≤ universalCeiling φ x := by
  have h : y ≤ (originalChild φ x).names.sup id := by
    simpa using (Finset.le_sup (f := id) hy)
  unfold universalCeiling
  omega

/-- Unconditionally construct the guarded PA universal-distribution leaf.
All scope changes are finite K proofs, including the common-binder alignment. -/
noncomputable def allImp (φ ψ : Peano.Formula) (x : Nat) :
    KDerivation (guardedCode ((FOL.allAt x (φ.imp ψ)).imp
      ((FOL.allAt x φ).imp (FOL.allAt x ψ)))) := by
  let z := jointName φ ψ x
  have hi : universalCeiling (φ.imp ψ) x < z := by dsimp [z, jointName]; omega
  have hφ : universalCeiling φ x < z := by dsimp [z, jointName]; omega
  have hψ : universalCeiling ψ x < z := by dsimp [z, jointName]; omega
  have align (θ : Peano.Formula) (hθ : universalCeiling θ x < z) :
      KDerivation (imp (code (FOL.allAt x θ)) (PAtoCompactGuardedAllImp.commonAll x θ z)) ×
      KDerivation (imp (PAtoCompactGuardedAllImp.commonAll x θ z) (code (FOL.allAt x θ))) := by
    have ht : topName x θ < z := lt_of_le_of_lt (ceiling_top θ x) hθ
    have hn : z ∉ (originalChild θ x).names := by
      intro hz
      have := ceiling_child θ x z hz
      omega
    have h := align_at θ x z ht hn
    simpa [PAtoCompactVacuousQuantifierFree.KBoth, PAtoCompactGuardedAllImp.commonAll, bodyAt,
      PAtoCompactGuardedAllImpAlignment.commonAll, Formula.encode, code] using h
  exact translated_allImp_at φ ψ x z (align _ hi).1 (align _ hφ).1 (align _ hψ).2

theorem allImp_certificate (φ ψ : Peano.Formula) (x : Nat) :
    theoremCode (certificate (allImp φ ψ x)) =
      guardedCode ((FOL.allAt x (φ.imp ψ)).imp ((FOL.allAt x φ).imp (FOL.allAt x ψ))) :=
  certificate_correct _

/-- Logical families still required after constructing universal distribution.
Every field is explicit finite K proof data; nothing asserts their existence. -/
structure FourLogical where
  allElim : ∀ (φ : Peano.Formula) (x : Nat) (t : Peano.Term),
    KDerivation (guardedCode ((FOL.allAt x φ).imp (FOL.substAt φ x t)))
  vacuous : ∀ (φ : Peano.Formula) (x : Nat), x ∉ φ.freeVarFinset →
    KDerivation (guardedCode (φ.imp (FOL.allAt x φ)))
  eqRefl : ∀ (t : Peano.Term), KDerivation (guardedCode (t.equal t))
  eqSubst : ∀ (φ : Peano.Formula) (x : Nat) (t u : Peano.Term),
    KDerivation (guardedCode ((t.equal u).imp ((FOL.substAt φ x t).imp (FOL.substAt φ x u))))

/-- Supply the proven allImp family to the existing logical handler interface. -/
noncomputable def remainingLogical (h : FourLogical) :
    PAtoCompactGuardedPropositional.RemainingLogical where
  allElim := h.allElim
  allImp := allImp
  vacuous := h.vacuous
  eqRefl := h.eqRefl
  eqSubst := h.eqSubst

end PASoundness.PAtoCompactGuardedAllImp

#print axioms PASoundness.PAtoCompactGuardedAllImp.guardedAllDistribution
#print axioms PASoundness.PAtoCompactGuardedAllImp.bodyAt_imp
#print axioms PASoundness.PAtoCompactGuardedAllImp.translated_allImp_at
#print axioms PASoundness.PAtoCompactGuardedAllImp.allImp
#print axioms PASoundness.PAtoCompactGuardedAllImp.allImp_certificate
#print axioms PASoundness.PAtoCompactGuardedAllImp.remainingLogical
