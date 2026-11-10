import PASoundness.PAtoCompactRestrictionEdgeReverse
import PASoundness.PAtoCompactRestrictionFilterVacuity
import PASoundness.PAtoCompactGraphVacuity19

/-! Reverse edge preservation with the K vacuity proofs supplied explicitly
by named-syntax freshness and bound-witness alpha conversion. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictionEdgeReverseClosed
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactRestrictionFilterVacuity

/-- The endpoint-filtered graph contains no edge absent from the source.
The explicit named-syntax side condition includes every binder and free
name in the filter. The intended reading of the three graph parameters also
requires that they avoid graph/pair binder names 19–22. This is not a proof
of endpoint preservation, graph existence, or quotient injectivity. -/
def restricted_edge_source (g h t x y u v : Nat)
    (ht19 : t ≠ 19) (hth : t ≠ h) (htg : t ≠ g)
    (fresh : 19 ∉ (namedFilter g h t x y).names) :
    KDerivation (imp (filterGraph g h t (edgePredicate t x y).encode)
      (imp (graphFormula h u v).encode (graphFormula g u v).encode)) :=
  PAtoCompactRestrictionEdgeReverse.restricted_edge_source g h t
    (edgePredicate t x y).encode u v ht19 hth htg
    (restriction_filter_vacuity g h t x y 19 fresh)
    (PAtoCompactGraphVacuity19.graph_vacuity_19 g u v)

/-- Certificate for the displayed K implication. -/
theorem restricted_edge_source_certificate (g h t x y u v : Nat)
    (ht19 : t ≠ 19) (hth : t ≠ h) (htg : t ≠ g)
    (fresh : 19 ∉ (namedFilter g h t x y).names) :
    theoremCode (certificate (restricted_edge_source g h t x y u v ht19 hth htg fresh)) =
      imp (filterGraph g h t (edgePredicate t x y).encode)
        (imp (graphFormula h u v).encode (graphFormula g u v).encode) :=
  certificate_correct (restricted_edge_source g h t x y u v ht19 hth htg fresh)

end PASoundness.PAtoCompactRestrictionEdgeReverseClosed

#print axioms PASoundness.PAtoCompactRestrictionEdgeReverseClosed.restricted_edge_source
