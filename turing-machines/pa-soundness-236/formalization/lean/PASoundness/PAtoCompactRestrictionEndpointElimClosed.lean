import PASoundness.PAtoCompactRestrictionEndpointElim
import PASoundness.PAtoCompactRestrictionEndpointVacuity
import PASoundness.PAtoCompactRestrictionPairVacuity

/-! Endpoint-witness elimination under explicit capture-safe label conditions. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictionEndpointElimClosed
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactRestrictionEndpointElim
open PASoundness.PAtoCompactRestrictionEndpointVacuity PASoundness.PAtoCompactRestrictionPairVacuity

/-- The same represented pair in the restriction predicate and supplied
edge gives endpoint membership. Witness labels 25 and 26 must avoid x,y;
the separate pair condition requires the displayed pair labels to be fresh.
The x,y labels may equal u,v, and represented objects may coincide. -/
def endpoints_from_predicate (x y u v : Nat)
    (pairFresh : [19,25,26,u,v,20,21,22,23,24].Nodup)
    (hx25 : 25 ≠ x) (hx26 : 26 ≠ x) (hy25 : 25 ≠ y) (hy26 : 26 ≠ y) :
    KDerivation (imp (pairFormula 19 u v).encode
      (imp (edgePredicate 19 x y).encode (both (member x u) (member y v)))) := by
  have hu25 : 25 ≠ u := by intro he; subst u; simp at pairFresh
  have hv25 : 25 ≠ v := by intro he; subst v; simp at pairFresh
  have hu26 : 26 ≠ u := by intro he; subst u; simp at pairFresh
  have hv26 : 26 ≠ v := by intro he; subst v; simp at pairFresh
  exact PAtoCompactRestrictionEndpointElim.endpoints_from_predicate x y u v pairFresh
    (pair_vacuity u v 25 (by decide) hu25 hv25 (by decide) (by decide) (by decide))
    (pair_vacuity u v 26 (by decide) hu26 hv26 (by decide) (by decide) (by decide))
    (first_member_vacuity_26 x hx26)
    (endpoints_vacuity x y u v 25 hx25 hy25 hu25 hv25)
    (endpoints_vacuity x y u v 26 hx26 hy26 hu26 hv26)

/-- Certificate for the displayed K implication. -/
theorem endpoints_from_predicate_certificate (x y u v : Nat)
    (pairFresh : [19,25,26,u,v,20,21,22,23,24].Nodup)
    (hx25 : 25 ≠ x) (hx26 : 26 ≠ x) (hy25 : 25 ≠ y) (hy26 : 26 ≠ y) :
    theoremCode (certificate (endpoints_from_predicate x y u v pairFresh hx25 hx26 hy25 hy26)) =
      imp (pairFormula 19 u v).encode
        (imp (edgePredicate 19 x y).encode (both (member x u) (member y v))) :=
  certificate_correct (endpoints_from_predicate x y u v pairFresh hx25 hx26 hy25 hy26)

end PASoundness.PAtoCompactRestrictionEndpointElimClosed

#print axioms PASoundness.PAtoCompactRestrictionEndpointElimClosed.endpoints_from_predicate
