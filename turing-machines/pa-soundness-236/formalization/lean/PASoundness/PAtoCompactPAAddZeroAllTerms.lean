import PASoundness.PAtoCompactPAAddZeroAxiomClosed
import PASoundness.PAtoCompactAllTermsTotalityClosed

/-! The guarded PA addition-zero axiom for every PA term, obtained by
supplying the actual finite-K child-graph witness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PASoundness.PAtoCompactPAAddZeroAllTerms

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactUnaryGuardedCanonical
open PASoundness.PAtoCompactVacuousEqualityAlignment

/-- For every PA term, construct a finite K proof of the literal guarded
addition-zero axiom. The graph-existence proof is supplied internally. -/
noncomputable def add_zero (t : Peano.Term) :
    KDerivation (guardedCode ((Peano.add t Peano.zero).equal t)) := by
  let A := (Peano.add t Peano.zero).equal t
  have hcover : ∀ a ∈ t.varFinset, id a ∈ A.freeVarFinset := by
    intro a ha
    simp only [id_eq, A, eq_free, Finset.mem_union]
    exact Or.inr ha
  have htotal := PASoundness.PAtoCompactAllTermsTotalityClosed.canonical_total id A t hcover
  apply PASoundness.PAtoCompactPAAddZeroAxiomClosed.add_zero_of_child t
  simpa [A, outputName, allocatorBase] using htotal

theorem add_zero_certificate (t : Peano.Term) :
    theoremCode (certificate (add_zero t)) =
      guardedCode ((Peano.add t Peano.zero).equal t) := certificate_correct _

end PASoundness.PAtoCompactPAAddZeroAllTerms

#print axioms PASoundness.PAtoCompactPAAddZeroAllTerms.add_zero
#print axioms PASoundness.PAtoCompactPAAddZeroAllTerms.add_zero_certificate
