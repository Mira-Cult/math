import PASoundness.PAtoCompactAllTermsAllElimFromFixed
import PASoundness.PAtoCompactMultiplicationCandidateTotalityClosed

/-! Guarded universal elimination for arbitrary PA terms with generated graph
existence supplied by finite K addition and multiplication proofs. The K-level
substitution compatibility implication remains an explicit proof input when
the eliminated variable occurs; the unused case needs no such input. This is
not an unconditional universal-elimination handler or a PA soundness bridge. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAllTermsAllElimWithTotality
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedAllElim PASoundness.PAtoCompactUnaryGuardedCanonical
open PASoundness.PAtoCompactFormulaTranslation

/-- For any PA term, K graph existence is supplied. The substitution bridge is
still an explicit finite K proof input exactly in the nonvacuous case. -/
noncomputable def allElim (φ : Peano.Formula) (x : Nat) (t : Peano.Term)
    (substitution : x ∈ φ.freeVarFinset → KDerivation (imp
      (guardFormula (allElimFormula φ x t)).encode
      (imp (termGraph id t (outputName (allElimFormula φ x t))
        (allocatorBase (allElimFormula φ x t))).encode
        (imp (instanceBody φ x (outputName (allElimFormula φ x t))).encode
          (code (FOL.substAt φ x t)))))) :
    KDerivation (guardedCode (allElimFormula φ x t)) := by
  apply PAtoCompactAllTermsAllElimFromFixed.allElim φ x t _ substitution
  intro _
  exact PAtoCompactMultiplicationCandidateTotalityClosed.candidate_total

theorem allElim_certificate (φ : Peano.Formula) (x : Nat) (t : Peano.Term)
    (substitution : x ∈ φ.freeVarFinset → KDerivation (imp
      (guardFormula (allElimFormula φ x t)).encode
      (imp (termGraph id t (outputName (allElimFormula φ x t))
        (allocatorBase (allElimFormula φ x t))).encode
        (imp (instanceBody φ x (outputName (allElimFormula φ x t))).encode
          (code (FOL.substAt φ x t)))))) :
    theoremCode (certificate (allElim φ x t substitution)) =
      guardedCode (allElimFormula φ x t) := certificate_correct _
end PASoundness.PAtoCompactAllTermsAllElimWithTotality
#print axioms PASoundness.PAtoCompactAllTermsAllElimWithTotality.allElim
#print axioms PASoundness.PAtoCompactAllTermsAllElimWithTotality.allElim_certificate
