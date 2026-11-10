import PASoundness.PAtoCompactGuardBaseTransport

/-! Candidate-binder transport for the first-factor multiplication induction
instance. This is a finite K conversion between two domain guards; it does
not prove any multiplication axiom, totality, or PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationInductionCandidateBridge
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactCandidateFieldTransport PASoundness.PAtoCompactCandidateBinderBridge
open PASoundness.PAtoCompactGuardBaseTransport
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Convert the allocated domain guard for name 200 to the exact binder
allocation of the multiplication induction instance. -/
def induction_candidate_bridge : KDerivation (imp (domainAt 300 200).encode
    (candidateCode 200 213 209 210 202 31 203 205 206)) := by
  rw [domainAt_encode]
  have h1 := transitivity_field 200 332 333 334 335 336 337 338 339 209 210 (by decide)
  have h2 := member_field 200 332 209 210 335 336 337 338 339 213 (by decide)
  have h3 := subset_field 200 213 209 210 335 336 337 338 339 202 (by decide) (by decide)
  have h4 := subset_test_field 200 213 209 210 202 336 337 338 339 31 (by decide) (by decide)
  have h5 := nonempty_field 200 213 209 210 202 31 337 338 339 203 (by decide)
  have h6 := witness_field 200 213 209 210 202 31 203 338 339 205 (by decide) (by decide)
  have h7 := order_field 200 213 209 210 202 31 203 205 339 206 (by decide) (by decide)
  exact compose h1 (compose h2 (compose h3 (compose h4 (compose h5 (compose h6 h7)))))

theorem induction_candidate_bridge_certificate : theoremCode (certificate induction_candidate_bridge) =
    imp (domainAt 300 200).encode (candidateCode 200 213 209 210 202 31 203 205 206) :=
  certificate_correct induction_candidate_bridge
end PASoundness.PAtoCompactMultiplicationInductionCandidateBridge
#print axioms PASoundness.PAtoCompactMultiplicationInductionCandidateBridge.induction_candidate_bridge
#print axioms PASoundness.PAtoCompactMultiplicationInductionCandidateBridge.induction_candidate_bridge_certificate
