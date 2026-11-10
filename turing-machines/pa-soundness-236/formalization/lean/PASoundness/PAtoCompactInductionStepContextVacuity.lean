import PASoundness.PAtoCompactGuardedVacuity

/-! Vacuity of the actual translated PA induction-step antecedent together
with the induction axiom's parameter guard. This is K proof data; it does not
identify the translated step with any candidate-domain step schema. -/
namespace PASoundness.PAtoCompactInductionStepContextVacuity

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedVacuity
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity

/-- The exact PA step appearing as the second antecedent of induction. -/
def paStep (φ : Peano.Formula) (x : Nat) : Peano.Formula :=
  FOL.allAt x (φ.imp (FOL.substAt φ x (Peano.succ (.var x))))

/-- The translated step with the free-variable guard of its induction axiom. -/
def paStepContext (φ : Peano.Formula) (x : Nat) : CompactNamed.Formula :=
  andF (guardFormula (Peano.inductionAxiom φ x)) (formula (paStep φ x))

/-- Every free variable of the PA step is free in the whole induction axiom. -/
theorem paStep_free_subset (φ : Peano.Formula) (x : Nat) :
    (paStep φ x).freeVarFinset ⊆ (Peano.inductionAxiom φ x).freeVarFinset := by
  intro z hz
  simp [Peano.inductionAxiom, paStep, BoundedFormula.freeVarFinset] at hz ⊢
  tauto

/-- The translated step context introduces no new free names. -/
theorem paStepContext_free_subset (φ : Peano.Formula) (x : Nat) :
    (paStepContext φ x).free ⊆ (Peano.inductionAxiom φ x).freeVarFinset := by
  rw [paStepContext, andF_free]
  exact Finset.union_subset (guardFormula_free_subset _) ((formula_free_subset _).trans (paStep_free_subset φ x))

/-- Finite K vacuity follows from freshness for the PA induction axiom's free
variables, even if the name is used by a bound translated variable. -/
def paStepContext_vacuity (φ : Peano.Formula) (x z : Nat)
    (fresh : z ∉ (Peano.inductionAxiom φ x).freeVarFinset) :
    KDerivation (imp (paStepContext φ x).encode (allCode z (paStepContext φ x).encode)) :=
  free_vacuity z (paStepContext φ x) (fun hz => fresh (paStepContext_free_subset φ x hz))

theorem paStepContext_vacuity_certificate (φ : Peano.Formula) (x z : Nat)
    (fresh : z ∉ (Peano.inductionAxiom φ x).freeVarFinset) :
    theoremCode (certificate (paStepContext_vacuity φ x z fresh)) =
      imp (paStepContext φ x).encode (allCode z (paStepContext φ x).encode) :=
  certificate_correct (paStepContext_vacuity φ x z fresh)

end PASoundness.PAtoCompactInductionStepContextVacuity

#print axioms PASoundness.PAtoCompactInductionStepContextVacuity.paStep_free_subset
#print axioms PASoundness.PAtoCompactInductionStepContextVacuity.paStepContext_free_subset
#print axioms PASoundness.PAtoCompactInductionStepContextVacuity.paStepContext_vacuity
#print axioms PASoundness.PAtoCompactInductionStepContextVacuity.paStepContext_vacuity_certificate
