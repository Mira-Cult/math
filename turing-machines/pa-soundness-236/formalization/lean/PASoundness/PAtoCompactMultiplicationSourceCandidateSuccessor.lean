import PASoundness.PAtoCompactCandidateFixed
import PASoundness.PAtoCompactGuardBaseTransport

/-! Candidate closure for the exact source successor used in the fixed-name
multiplication induction. This derives a candidate guard from a supplied raw
successor; it does not construct a multiplication graph or prove totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationSourceCandidateSuccessor
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactCandidateFixed PASoundness.PAtoCompactGuardBaseTransport
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The raw successor of a candidate, at the exact multiplication labels, is
itself a candidate at the same allocation base. -/
def source_candidate_successor : KDerivation
    (imp (domainAt 300 204).encode (imp (successorCode 204 205 208)
      (domainAt 300 205).encode)) := by
  have h := fixed_candidate_successor 204 205 208 332 333 334 400 401 402
    335 336 338 339 403 337 404 405 406 407 (by decide)
  simpa only [domainAt_encode] using h

theorem source_candidate_successor_certificate :
    theoremCode (certificate source_candidate_successor) =
      imp (domainAt 300 204).encode (imp (successorCode 204 205 208)
        (domainAt 300 205).encode) := certificate_correct source_candidate_successor
end PASoundness.PAtoCompactMultiplicationSourceCandidateSuccessor
#print axioms PASoundness.PAtoCompactMultiplicationSourceCandidateSuccessor.source_candidate_successor
#print axioms PASoundness.PAtoCompactMultiplicationSourceCandidateSuccessor.source_candidate_successor_certificate
