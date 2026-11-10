import PASoundness.PAtoCompactProductMatchAllocatedCongruence
import PASoundness.PAtoCompactDomainCandidateReverse

/-! Replace the fixed internal-name candidate premise in allocated product
congruence by the allocator-indexed domain guard for the same source output. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchDomainCongruence

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactDomainCandidateReverse PASoundness.PAtoCompactProductMatchAllocatedCongruence

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

noncomputable def domain_product_congruence (b : Nat) (hb : 44 < b + 2) : KDerivation
    (imp (mulAt b 0 1 2).encode (imp (mulAt b 42 43 44).encode
      (imp (equivAt b 0 42).encode (imp (equivAt b 1 43).encode
        (imp (domainAt b 2).encode (equivAt b 2 44).encode))))) := by
  have hc := domain_to_candidate 2 81 77 78 72 64 73 59 75 b (by decide) (by omega)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(domainAt b 2).encode,(equivAt b 1 43).encode,(equivAt b 0 42).encode,
    (mulAt b 42 43 44).encode,(mulAt b 0 1 2).encode]
  have hd : Context Γ (domainAt b 2).encode := .head _ _
  have he₂ : Context Γ (equivAt b 1 43).encode := .hypothesis (by simp [Γ])
  have he₁ : Context Γ (equivAt b 0 42).encode := .hypothesis (by simp [Γ])
  have ht : Context Γ (mulAt b 42 43 44).encode := .hypothesis (by simp [Γ])
  have hs : Context Γ (mulAt b 0 1 2).encode := .hypothesis (by simp [Γ])
  have h := Context.mp (Context.mp hd (.closed hc)) (Context.mp he₂ (Context.mp he₁
    (Context.mp ht (Context.mp hs (.closed (allocated_product_congruence_at b hb))))))
  simpa [Γ] using h

theorem domain_product_congruence_certificate (b : Nat) (hb : 44 < b + 2) :
    theoremCode (certificate (domain_product_congruence b hb)) =
      imp (mulAt b 0 1 2).encode (imp (mulAt b 42 43 44).encode
        (imp (equivAt b 0 42).encode (imp (equivAt b 1 43).encode
          (imp (domainAt b 2).encode (equivAt b 2 44).encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchDomainCongruence

#print axioms PASoundness.PAtoCompactProductMatchDomainCongruence.domain_product_congruence
#print axioms PASoundness.PAtoCompactProductMatchDomainCongruence.domain_product_congruence_certificate
