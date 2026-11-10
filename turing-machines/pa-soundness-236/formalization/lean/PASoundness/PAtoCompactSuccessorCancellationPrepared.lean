import PASoundness.PAtoCompactRestrictedFromEquivalent
import PASoundness.PAtoCompactRestrictedEquivalentTarget

/-! Successor graph restriction, expressed with the explicitly alpha-prepared
endpoint formula. No K substitution principle is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccessorCancellationPrepared
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactRestrictedFromEquivalent
open PASoundness.PAtoCompactRestrictedEquivalentTarget
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Actual K proof with the original equivalent formula at 0,1 and the
explicitly prepared target at 2,5. Transitivity is only assumed for 5;
the two supplied successor graphs are at 0,1. -/
def successor_cancellation_prepared : KDerivation
    (imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp (transitiveCode 5 11 12)
        (imp equivalentFormula.encode endpointTarget.encode)))) := by
  rw [endpoint_target_code]
  exact restricted_from_equivalent

theorem successor_cancellation_prepared_certificate :
    theoremCode (certificate successor_cancellation_prepared) =
      imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
        (imp (transitiveCode 5 11 12)
          (imp equivalentFormula.encode endpointTarget.encode))) :=
  certificate_correct successor_cancellation_prepared

end PASoundness.PAtoCompactSuccessorCancellationPrepared

#print axioms PASoundness.PAtoCompactSuccessorCancellationPrepared.successor_cancellation_prepared
#print axioms PASoundness.PAtoCompactSuccessorCancellationPrepared.successor_cancellation_prepared_certificate
