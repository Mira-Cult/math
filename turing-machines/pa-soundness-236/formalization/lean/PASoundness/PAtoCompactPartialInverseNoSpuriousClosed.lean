import PASoundness.PAtoCompactPartialInverseNoSpurious
import PASoundness.PAtoCompactPartialInversePairAliasSymm

/-! Discharge the explicit pair-alias proof argument of the no-spurious-edge
lemma with the actual K coordinate-injectivity derivation. Adjunction and the
appended pair remain displayed object-level hypotheses; no inverse graph
existence or induction is claimed. -/
namespace PASoundness.PAtoCompactPartialInverseNoSpuriousClosed
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactPartialInverseVacuitySymm PASoundness.PAtoCompactPartialInverseNoSpurious
open PASoundness.PAtoCompactPartialInversePairAliasSymm

/-- Under the supplied adjunction and appended-pair graphs, a new reverse edge
was already present or has the appended pair's coordinates. -/
def no_spurious_edge_closed : KDerivation
    (imp (adjoinCode 7 11 9 14) (imp (pairFormula 11 13 12).encode
      (imp (graphFormula 9 3 2).encode conclusion.encode))) :=
  no_spurious_edge reversed_new_edge_symm

theorem no_spurious_edge_closed_certificate :
    theoremCode (certificate no_spurious_edge_closed) =
      imp (adjoinCode 7 11 9 14) (imp (pairFormula 11 13 12).encode
        (imp (graphFormula 9 3 2).encode conclusion.encode)) :=
  certificate_correct no_spurious_edge_closed

end PASoundness.PAtoCompactPartialInverseNoSpuriousClosed

#print axioms PASoundness.PAtoCompactPartialInverseNoSpuriousClosed.no_spurious_edge_closed
#print axioms PASoundness.PAtoCompactPartialInverseNoSpuriousClosed.no_spurious_edge_closed_certificate
