import PASoundness.PAtoCompactRawSuccBridge
import PASoundness.PAtoCompactCandidateAlpha
import PASoundness.PAtoCompactLessRightSegmentAliases

/-! Extract and alpha-rename the transitivity fields needed by member-cut
transport from the two explicitly supplied output-domain predicates. -/
namespace PASoundness.PAtoCompactMemberOutputDomainsTrans
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactRawSuccBridge
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactCandidateAlpha PASoundness.PAtoCompactLessRightSegmentAliases
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Source output 32 has the transitivity field at fresh test names 11,12. -/
def source_output_transitive : KDerivation
    (imp (domainAt 100 32).encode (namedTrans 32 11 12).encode) := by
  have h := candidate_transitive_frame 100 33 32 (by decide) (by decide) (by decide)
  have h' : KDerivation (imp (domainAt 100 32).encode (transitiveCode 32 37 38)) := by
    simpa [namedTransitive,transitiveBody,transitiveCode,Formula.encode] using h
  have ht := compose h' (transitive_rename 32 37 38 11 12 (by decide))
  simpa [namedTrans,transitiveBody,transitiveCode,Formula.encode] using ht

/-- Target output 8 has the transitivity field at fresh test names 16,18. -/
def target_output_transitive : KDerivation
    (imp (domainAt 100 8).encode (namedTrans 8 16 18).encode) := by
  have h := candidate_transitive_frame 100 33 8 (by decide) (by decide) (by decide)
  have h' : KDerivation (imp (domainAt 100 8).encode (transitiveCode 8 37 38)) := by
    simpa [namedTransitive,transitiveBody,transitiveCode,Formula.encode] using h
  have ht := compose h' (transitive_rename 8 37 38 16 18 (by decide))
  simpa [namedTrans,transitiveBody,transitiveCode,Formula.encode] using ht

theorem source_output_transitive_certificate : theoremCode (certificate source_output_transitive) =
    imp (domainAt 100 32).encode (namedTrans 32 11 12).encode := certificate_correct _
theorem target_output_transitive_certificate : theoremCode (certificate target_output_transitive) =
    imp (domainAt 100 8).encode (namedTrans 8 16 18).encode := certificate_correct _
end PASoundness.PAtoCompactMemberOutputDomainsTrans

#print axioms PASoundness.PAtoCompactMemberOutputDomainsTrans.source_output_transitive
#print axioms PASoundness.PAtoCompactMemberOutputDomainsTrans.target_output_transitive
#print axioms PASoundness.PAtoCompactMemberOutputDomainsTrans.source_output_transitive_certificate
#print axioms PASoundness.PAtoCompactMemberOutputDomainsTrans.target_output_transitive_certificate
