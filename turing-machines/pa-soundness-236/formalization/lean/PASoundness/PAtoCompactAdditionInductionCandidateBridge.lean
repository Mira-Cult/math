import PASoundness.PAtoCompactGuardBaseTransport

/-! Capture-safe K candidate-binder transport for the fixed addition induction
endpoint at name 200. This is only a conversion between explicit candidate
guards; it does not prove addition totality or a PA bridge. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionInductionCandidateBridge
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactCandidateFieldTransport PASoundness.PAtoCompactCandidateBinderBridge
open PASoundness.PAtoCompactGuardBaseTransport
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The literal candidate guard on name 200 implies the exact alpha-renamed
candidate used by the fixed addition-induction instance. -/
def induction_candidate_bridge : KDerivation (imp (domainAt 100 200).encode
    (candidateCode 200 213 209 210 202 31 203 205 206)) := by
  rw [domainAt_encode]
  have h1 := transitivity_field 200 132 133 134 135 136 137 138 139 209 210 (by decide)
  have h2 := member_field 200 132 209 210 135 136 137 138 139 213 (by decide)
  have h3 := subset_field 200 213 209 210 135 136 137 138 139 202 (by decide) (by decide)
  have h4 := subset_test_field 200 213 209 210 202 136 137 138 139 31 (by decide) (by decide)
  have h5 := nonempty_field 200 213 209 210 202 31 137 138 139 203 (by decide)
  have h6 := witness_field 200 213 209 210 202 31 203 138 139 205 (by decide) (by decide)
  have h7 := order_field 200 213 209 210 202 31 203 205 139 206 (by decide) (by decide)
  exact compose h1 (compose h2 (compose h3 (compose h4 (compose h5 (compose h6 h7)))))

theorem induction_candidate_bridge_certificate : theoremCode (certificate induction_candidate_bridge) =
    imp (domainAt 100 200).encode (candidateCode 200 213 209 210 202 31 203 205 206) :=
  certificate_correct induction_candidate_bridge
end PASoundness.PAtoCompactAdditionInductionCandidateBridge
#print axioms PASoundness.PAtoCompactAdditionInductionCandidateBridge.induction_candidate_bridge
#print axioms PASoundness.PAtoCompactAdditionInductionCandidateBridge.induction_candidate_bridge_certificate
