import PASoundness.PAtoCompactGuardedVacuousAxiom

/-! Unconditional guarded vacuous-axiom proofs for the bottom/implication
fragment. This restricted fragment has no atomic arithmetic or quantifiers. -/
namespace PASoundness.PAtoCompactGuardedVacuousPure

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactHilbertBasis
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactGuardedVacuousAxiom

inductive Pure : Peano.Formula → Prop
  | falsum : Pure .falsum
  | imp {φ ψ : Peano.Formula} : Pure φ → Pure ψ → Pure (φ.imp ψ)

theorem free_empty {φ : Peano.Formula} (h : Pure φ) : φ.freeVarFinset = ∅ := by
  induction h with
  | falsum => rfl
  | imp hφ hψ ihφ ihψ => simp [BoundedFormula.freeVarFinset, ihφ, ihψ]

/-- Relabeling and the bound-name environment do not affect the translation
of a source formula in the bottom/implication fragment. -/
theorem scoped_relabel {φ : Peano.Formula} (h : Pure φ)
    (f : Nat → Nat ⊕ Fin 1) (bound : Fin 1 → Nat) :
    scopedFormula 1 (BoundedFormula.relabel f φ) bound = formula φ := by
  induction h with
  | falsum => rfl
  | imp hφ hψ ihφ ihψ =>
      simp only [BoundedFormula.relabel_imp, scopedFormula, formula] at *
      rw [← ihφ, ← ihψ]

theorem top_body_eq {φ : Peano.Formula} (h : Pure φ) (x : Nat) :
    topBody x φ = formula φ := by
  exact scoped_relabel h _ _

/-- Every formula in the restricted fragment has a finite K proof of the
guarded vacuous PA axiom, without an alignment assumption. -/
def vacuous (φ : Peano.Formula) (h : Pure φ) (x : Nat) :
    KDerivation (guardedCode (φ.imp (FOL.allAt x φ))) := by
  apply vacuous_of_body_alignment φ x
  · rw [free_empty h]; simp
  · rw [top_body_eq h]
    exact identity (code φ)

theorem vacuous_certificate (φ : Peano.Formula) (h : Pure φ) (x : Nat) :
    theoremCode (certificate (vacuous φ h x)) = guardedCode (φ.imp (FOL.allAt x φ)) :=
  certificate_correct _

end PASoundness.PAtoCompactGuardedVacuousPure

#print axioms PASoundness.PAtoCompactGuardedVacuousPure.free_empty
#print axioms PASoundness.PAtoCompactGuardedVacuousPure.scoped_relabel
#print axioms PASoundness.PAtoCompactGuardedVacuousPure.top_body_eq
#print axioms PASoundness.PAtoCompactGuardedVacuousPure.vacuous
#print axioms PASoundness.PAtoCompactGuardedVacuousPure.vacuous_certificate
