import PASoundness.PAtoCompactProductOutputAllocatedFixed
import PASoundness.PAtoCompactDomainCandidateReverse

/-! Replace the internal fixed-name candidate premise by the allocator-100
domain guard for the same actual source product output. This remains a
fixed-label relation-level transport theorem. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputFixedDomain

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactDomainCandidateReverse
open PASoundness.PAtoCompactProductOutputAllocatedFixed PASoundness.PAtoCompactCandidateExact

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Source domain0, source multiplication and ordered equivalence0→42 imply
target multiplication at the same ordered factor names43 and44. -/
noncomputable def fixed_domain_output : KDerivation
    (imp (mulAt 100 43 44 0).encode (imp (equivAt 100 0 42).encode
      (imp (domainAt 100 0).encode (mulAt 100 43 44 42).encode))) := by
  have hc := domain_to_candidate 0 81 77 78 72 64 73 59 75 100 (by decide) (by omega)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(domainAt 100 0).encode,(equivAt 100 0 42).encode,(mulAt 100 43 44 0).encode]
  have hd : Context Γ (domainAt 100 0).encode := .head _ _
  have he : Context Γ (equivAt 100 0 42).encode := .hypothesis (by simp [Γ])
  have hs : Context Γ (mulAt 100 43 44 0).encode := .hypothesis (by simp [Γ])
  have hcandidate := Context.mp hd (.closed hc)
  exact .mp hcandidate (.mp he (.mp hs (.closed allocated_fixed_output)))

theorem fixed_domain_output_certificate : theoremCode (certificate fixed_domain_output) =
    imp (mulAt 100 43 44 0).encode (imp (equivAt 100 0 42).encode
      (imp (domainAt 100 0).encode (mulAt 100 43 44 42).encode)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputFixedDomain

#print axioms PASoundness.PAtoCompactProductOutputFixedDomain.fixed_domain_output
#print axioms PASoundness.PAtoCompactProductOutputFixedDomain.fixed_domain_output_certificate
