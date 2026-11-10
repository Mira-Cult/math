import PASoundness.PAtoCompactPartialInverseOutsideExists
import PASoundness.PAtoCompactPartialInversePredicate

/-! Exact syntactic alignment of the outside-source partial-inverse step with
its capture-safe induction predicate. This proves only the displayed branch;
no global induction or inverse-graph construction is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseOutsidePredicate
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPartialInverseOutside
open PASoundness.PAtoCompactPartialInverseOutsideExists PASoundness.PAtoCompactPartialInversePredicate

/-- The successor-prefix instance contains the same graph existential and the
literal prefix substitution, with no change to the input-domain parameters. -/
theorem successor_instance : replace 30 10 predicate = .ex 7 nextPartialInverse := by decide

/-- When the old prefix lies outside the source domain, any existential
partial-inverse witness also witnesses the induction predicate at the supplied
successor prefix. -/
def outside_predicate_step : KDerivation
    (imp (successorCode 8 10 15) (imp (neg (member 0 8))
      (imp (replace 30 8 predicate).encode (replace 30 10 predicate).encode))) := by
  rw [instance_roundtrip, successor_instance]
  exact outside_successor_exists

theorem outside_predicate_step_certificate :
    theoremCode (certificate outside_predicate_step) =
      imp (successorCode 8 10 15) (imp (neg (member 0 8))
        (imp (replace 30 8 predicate).encode (replace 30 10 predicate).encode)) :=
  certificate_correct outside_predicate_step

end PASoundness.PAtoCompactPartialInverseOutsidePredicate

#print axioms PASoundness.PAtoCompactPartialInverseOutsidePredicate.outside_predicate_step
#print axioms PASoundness.PAtoCompactPartialInverseOutsidePredicate.outside_predicate_step_certificate
