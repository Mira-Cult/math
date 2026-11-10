import PASoundness.PAtoCompactGuardedBridge
import PASoundness.PAtoCompactFreeVacuity

/-! Free-name bounds and finite K vacuity for the actual guarded PA
translation. The resulting quantified open translation is not yet identified
with the separately allocated translation of `FOL.allAt`. -/
namespace PASoundness.PAtoCompactGuardedVacuity

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactGuardedBridge

/-- A free name in the guard conjunction occurs in its source list. -/
theorem guardList_free_subset (base : Nat) (xs : List Nat) :
    (guardList base xs).free ⊆ xs.toFinset := by
  induction xs with
  | nil => simp [guardList, Formula.free]
  | cons y ys ih =>
      simp only [guardList, andF_free, List.toFinset_cons]
      exact Finset.union_subset ((domainAt_free base y).trans (by simp))
        (ih.trans (Finset.subset_insert _ _))

/-- Every free name in the concrete guard occurs in the source formula. -/
theorem guardFormula_free_subset (φ : Peano.Formula) :
    (guardFormula φ).free ⊆ φ.freeVarFinset := by
  simpa [guardFormula] using guardList_free_subset (guardBase φ)
    (φ.freeVarFinset.sort (· ≤ ·))

/-- K proves that a guard is vacuous at a name absent from the source. -/
def guardFormula_vacuity (φ : Peano.Formula) (x : Nat) (hx : x ∉ φ.freeVarFinset) :
    KDerivation (imp (guardFormula φ).encode (allCode x (guardFormula φ).encode)) :=
  free_vacuity x (guardFormula φ) (fun h => hx (guardFormula_free_subset φ h))

/-- Generalize the already translated body under the same guard. This is
not the generalization handler: the literal translation of `FOL.allAt x φ`
uses separately allocated binders. -/
def generalize_guarded_body (φ : Peano.Formula) (x : Nat)
    (hx : x ∉ φ.freeVarFinset) (d : KDerivation (guardedCode φ)) :
    KDerivation (imp (guardFormula φ).encode (allCode x (code φ))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply generalizeOne x (guardFormula_vacuity φ x hx)
  exact .mp (Context.head [] _) (.closed d)

end PASoundness.PAtoCompactGuardedVacuity

#print axioms PASoundness.PAtoCompactGuardedVacuity.guardList_free_subset
#print axioms PASoundness.PAtoCompactGuardedVacuity.guardFormula_free_subset
#print axioms PASoundness.PAtoCompactGuardedVacuity.guardFormula_vacuity
#print axioms PASoundness.PAtoCompactGuardedVacuity.generalize_guarded_body
