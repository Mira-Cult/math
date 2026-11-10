import PASoundness.PAtoCompactZeroSuccessor
import PASoundness.CompactQuantifiers

/-! Capture-safe K vacuity for the endpoint conclusion of a graph filter. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictionEndpointVacuity
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A single K vacuity construction works for any witness name different
from the four displayed endpoint labels. These conditions concern syntax
names; no inequality between represented objects is assumed. -/
def endpoints_vacuity (x y u v q : Nat)
    (hqx : q ≠ x) (hqy : q ≠ y) (hqu : q ≠ u) (hqv : q ≠ v) :
    KDerivation (imp (both (member x u) (member y v))
      (allCode q (both (member x u) (member y v)))) := by
  let F := namedBoth (.member x u) (.member y v)
  have hf : q ∉ F.names := by
    simp [F, namedBoth, Formula.names, hqx, hqy, hqu, hqv,
      Ne.symm hqx, Ne.symm hqy, Ne.symm hqu, Ne.symm hqv]
  simpa [F, namedBoth, Formula.encode, CompactProof.both, CompactProof.neg] using F.vacuity q hf

theorem endpoints_vacuity_certificate (x y u v q : Nat)
    (hqx : q ≠ x) (hqy : q ≠ y) (hqu : q ≠ u) (hqv : q ≠ v) :
    theoremCode (certificate (endpoints_vacuity x y u v q hqx hqy hqu hqv)) =
      imp (both (member x u) (member y v))
        (allCode q (both (member x u) (member y v))) :=
  certificate_correct (endpoints_vacuity x y u v q hqx hqy hqu hqv)

end PASoundness.PAtoCompactRestrictionEndpointVacuity

#print axioms PASoundness.PAtoCompactRestrictionEndpointVacuity.endpoints_vacuity
