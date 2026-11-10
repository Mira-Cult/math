import PASoundness.PAtoCompactAdditionOutputStrongClosed
import PASoundness.PAtoCompactAdditionZeroAllocated

/-! Connect the literal-source guarded output transport proof to the
allocated addition source using its finite-K alpha conversion. The result
remains fixed-label and noncomputable; it is not a uniform term-graph law. -/
namespace PASoundness.PAtoCompactAdditionOutputAllocatedFixed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactAdditionZeroAllocated
open PASoundness.PAtoCompactAdditionOutputStrongCases PASoundness.PAtoCompactAdditionOutputStrongClosed
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The fixed source addition at allocator 100 transports its output under
all four displayed operand/output domain predicates and the supplied output
isomorphism. The syntactic labels denote objects that may coincide. -/
noncomputable def allocated_output_fixed : KDerivation
    (imp (addAt 100 30 31 32).encode
      (imp (domainAt 100 32).encode (imp (domainAt 100 8).encode
        (imp (domainAt 100 31).encode (imp (domainAt 100 30).encode
          (imp (PASoundness.PAtoCompactTermTranslation.equivAt 100 32 8).encode
            (addAt 100 30 31 8).encode)))))) := by
  have ha := (original_allocated_alpha 100 (by decide)).backward
  have hshape : PASoundness.PAtoCompactAddBaseInventory.addTemplate =
      PASoundness.PAtoCompactOrdinalAddition.additionFormula := by decide
  rw [hshape] at ha
  have h : KDerivation (imp (addAt 100 30 31 32).encode strongTarget.encode) :=
    compose ha addition_output_strong
  change KDerivation (imp (addAt 100 30 31 32).encode
      (imp (domainAt 100 32).encode (imp (domainAt 100 8).encode
        (imp (domainAt 100 31).encode (imp (domainAt 100 30).encode
          (imp (PASoundness.PAtoCompactTermTranslation.equivAt 100 32 8).encode
            (addAt 100 30 31 8).encode)))))) at h
  exact h

theorem allocated_output_fixed_certificate : theoremCode (certificate allocated_output_fixed) =
    imp (addAt 100 30 31 32).encode
      (imp (domainAt 100 32).encode (imp (domainAt 100 8).encode
        (imp (domainAt 100 31).encode (imp (domainAt 100 30).encode
          (imp (PASoundness.PAtoCompactTermTranslation.equivAt 100 32 8).encode
            (addAt 100 30 31 8).encode))))) := certificate_correct allocated_output_fixed
end PASoundness.PAtoCompactAdditionOutputAllocatedFixed

#print axioms PASoundness.PAtoCompactAdditionOutputAllocatedFixed.allocated_output_fixed
#print axioms PASoundness.PAtoCompactAdditionOutputAllocatedFixed.allocated_output_fixed_certificate
