import PASoundness.PAtoCompactRawSuccBridge

/-! Candidate guards supply exactly the whole-object transitivity premises
used by the addition-successor graph. No condition on the filtered suffix is
asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionDomainTransitivity
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactRawSuccBridge

/-- The candidate guard for old source 31 yields its transitivity at test
labels 37,38. -/
def source_transitive : KDerivation (imp (domainAt 100 31).encode (transitiveCode 31 37 38)) := by
  have h := candidate_transitive_frame 100 33 31 (by decide) (by decide) (by decide)
  simpa [namedTransitive, transitiveBody, transitiveCode, Formula.encode] using h

/-- The candidate guard for old result 32 yields its transitivity at the
same test labels; the old suffix is not assumed transitive. -/
def result_transitive : KDerivation (imp (domainAt 100 32).encode (transitiveCode 32 37 38)) := by
  have h := candidate_transitive_frame 100 33 32 (by decide) (by decide) (by decide)
  simpa [namedTransitive, transitiveBody, transitiveCode, Formula.encode] using h

theorem source_transitive_certificate : theoremCode (certificate source_transitive) =
    imp (domainAt 100 31).encode (transitiveCode 31 37 38) := certificate_correct source_transitive

theorem result_transitive_certificate : theoremCode (certificate result_transitive) =
    imp (domainAt 100 32).encode (transitiveCode 32 37 38) := certificate_correct result_transitive
end PASoundness.PAtoCompactAdditionDomainTransitivity
#print axioms PASoundness.PAtoCompactAdditionDomainTransitivity.source_transitive
#print axioms PASoundness.PAtoCompactAdditionDomainTransitivity.result_transitive
#print axioms PASoundness.PAtoCompactAdditionDomainTransitivity.source_transitive_certificate
#print axioms PASoundness.PAtoCompactAdditionDomainTransitivity.result_transitive_certificate
