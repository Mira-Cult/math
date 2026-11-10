import PASoundness.PAtoCompactGuardBaseTransport

/-! Exact predecessor-candidate guard alignment for first-factor multiplication
induction. This is finite K proof data, independent of a multiplication
successor law or semantic soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationPredecessorDomainAlign
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactCandidateFieldTransport PASoundness.PAtoCompactCandidateBinderBridge
open PASoundness.PAtoCompactGuardBaseTransport
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Convert the predecessor candidate from the candidate-restricted induction
step to the precise domain guard at multiplication's allocation base. -/
def predecessor_guard_align : KDerivation
    (imp (candidateCode 204 230 209 210 232 31 203 231 206)
      (domainAt 300 204).encode) := by
  have h1 := transitivity_field 204 230 209 210 232 31 203 231 206 333 334 (by decide)
  have h2 := member_field 204 230 333 334 232 31 203 231 206 332 (by decide)
  have h3 := subset_field 204 332 333 334 232 31 203 231 206 335 (by decide) (by decide)
  have h4 := subset_test_field 204 332 333 334 335 31 203 231 206 336 (by decide) (by decide)
  have h5 := nonempty_field 204 332 333 334 335 336 203 231 206 337 (by decide)
  have h6 := witness_field 204 332 333 334 335 336 337 231 206 338 (by decide) (by decide)
  have h7 := order_field 204 332 333 334 335 336 337 338 206 339 (by decide) (by decide)
  rw [domainAt_encode]
  exact compose h1 (compose h2 (compose h3 (compose h4 (compose h5 (compose h6 h7)))))

theorem predecessor_guard_align_certificate : theoremCode (certificate predecessor_guard_align) =
    imp (candidateCode 204 230 209 210 232 31 203 231 206)
      (domainAt 300 204).encode := certificate_correct predecessor_guard_align
end PASoundness.PAtoCompactMultiplicationPredecessorDomainAlign
#print axioms PASoundness.PAtoCompactMultiplicationPredecessorDomainAlign.predecessor_guard_align
#print axioms PASoundness.PAtoCompactMultiplicationPredecessorDomainAlign.predecessor_guard_align_certificate
