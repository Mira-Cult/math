import PASoundness.PAtoCompactPartialCompositionOutsideExists
import PASoundness.PAtoCompactPartialCompositionPredicate

/-! Exact capture-safe induction-predicate alignment for the outside-source
partial-composition successor branch. It retains the same graph witness and
does not establish the inside branch, graph collection or transitivity. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionOutsidePredicate
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPartialCompositionOutside
open PASoundness.PAtoCompactPartialCompositionOutsideExists PASoundness.PAtoCompactPartialCompositionPredicate

/-- The new predicate instance is the same existential graph with only its
prefix label changed. -/
theorem successor_instance : replace 30 13 predicate = .ex 9 nextPartialComposition := by decide

/-- Outside-source successor step in the exact induction-predicate syntax. -/
def outside_predicate_step : KDerivation
    (imp (successorCode 10 13 15) (imp (neg (member 0 10))
      (imp (replace 30 10 predicate).encode (replace 30 13 predicate).encode))) := by
  rw [instance_roundtrip, successor_instance]
  exact outside_successor_exists

theorem outside_predicate_step_certificate :
    theoremCode (certificate outside_predicate_step) =
      imp (successorCode 10 13 15) (imp (neg (member 0 10))
        (imp (replace 30 10 predicate).encode (replace 30 13 predicate).encode)) :=
  certificate_correct outside_predicate_step

end PASoundness.PAtoCompactPartialCompositionOutsidePredicate

#print axioms PASoundness.PAtoCompactPartialCompositionOutsidePredicate.outside_predicate_step
#print axioms PASoundness.PAtoCompactPartialCompositionOutsidePredicate.outside_predicate_step_certificate
