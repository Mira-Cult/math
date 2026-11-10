import PASoundness.PAtoCompactAllTermsTotalityFromFixedMultiplication
import PASoundness.PAtoCompactAllElimVariable

/-! Guarded universal elimination for arbitrary PA terms, conditional on the
explicit fixed multiplication-existence proof and K-level substitution
compatibility. Both inputs are needed only when the replaced variable occurs.
This does not establish either input or the full PA bridge. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAllTermsAllElimFromFixed
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedAllElim PASoundness.PAtoCompactAllElimVariable
open PASoundness.PAtoCompactUnaryGuardedCanonical PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactAllTermsTotalityFromFixedMultiplication

/-- If the source variable occurs, the axiom guard covers every free variable
of the substituting term. The graph witness follows from the supplied finite K
multiplication-existence proof; substitution compatibility remains explicit. -/
noncomputable def allElim_of_substitution (φ : Peano.Formula) (x : Nat)
    (t : Peano.Term) (hx : x ∈ φ.freeVarFinset)
    (fixed : KDerivation fixedMultiplication)
    (substitution : KDerivation (imp (guardFormula (allElimFormula φ x t)).encode
      (imp (termGraph id t (outputName (allElimFormula φ x t))
        (allocatorBase (allElimFormula φ x t))).encode
        (imp (instanceBody φ x (outputName (allElimFormula φ x t))).encode
          (code (FOL.substAt φ x t)))))) :
    KDerivation (guardedCode (allElimFormula φ x t)) := by
  let A := allElimFormula φ x t
  have hc : ∀ a ∈ t.varFinset, id a ∈ A.freeVarFinset := by
    intro a ha
    exact termVars_in_axiom_of_occurs φ x t hx ha
  apply allElim_of_witness φ x t (outputName A) (termGraph id t (outputName A) (allocatorBase A))
    (outputName_guard_fresh φ x t) (outputName_all_fresh φ x t) (outputName_target_fresh φ x t)
  · exact PAtoCompactAllTermsTotalityFromFixedMultiplication.canonical_total id A t fixed hc
  · exact substitution

/-- Every PA substitution term is admitted. For an unused source variable,
no term graph or substitution-compatibility proof is needed; otherwise both
explicit K proof inputs are required. -/
noncomputable def allElim (φ : Peano.Formula) (x : Nat) (t : Peano.Term)
    (fixed : x ∈ φ.freeVarFinset → KDerivation fixedMultiplication)
    (substitution : x ∈ φ.freeVarFinset → KDerivation (imp
      (guardFormula (allElimFormula φ x t)).encode
      (imp (termGraph id t (outputName (allElimFormula φ x t))
        (allocatorBase (allElimFormula φ x t))).encode
        (imp (instanceBody φ x (outputName (allElimFormula φ x t))).encode
          (code (FOL.substAt φ x t)))))) :
    KDerivation (guardedCode (allElimFormula φ x t)) := by
  by_cases hx : x ∈ φ.freeVarFinset
  · exact allElim_of_substitution φ x t hx (fixed hx) (substitution hx)
  · exact PAtoCompactVacuousAllElim.allElim_of_unused φ x t hx

theorem allElim_certificate (φ : Peano.Formula) (x : Nat) (t : Peano.Term)
    (fixed : x ∈ φ.freeVarFinset → KDerivation fixedMultiplication)
    (substitution : x ∈ φ.freeVarFinset → KDerivation (imp
      (guardFormula (allElimFormula φ x t)).encode
      (imp (termGraph id t (outputName (allElimFormula φ x t))
        (allocatorBase (allElimFormula φ x t))).encode
        (imp (instanceBody φ x (outputName (allElimFormula φ x t))).encode
          (code (FOL.substAt φ x t)))))) :
    theoremCode (certificate (allElim φ x t fixed substitution)) =
      guardedCode (allElimFormula φ x t) := certificate_correct _
end PASoundness.PAtoCompactAllTermsAllElimFromFixed
#print axioms PASoundness.PAtoCompactAllTermsAllElimFromFixed.allElim_of_substitution
#print axioms PASoundness.PAtoCompactAllTermsAllElimFromFixed.allElim
#print axioms PASoundness.PAtoCompactAllTermsAllElimFromFixed.allElim_certificate
