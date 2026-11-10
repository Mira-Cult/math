import PASoundness.PAtoCompactSuccCongruenceBijection
import PASoundness.PAtoCompactSuccLeftOldPremises
import PASoundness.PAtoCompactSuccBijectionLeftClosed
import PASoundness.PAtoCompactSuccBijectionRightClosed
import PASoundness.PAtoCompactSuccBijectionRightTopCompose

/-! Successor-bijection matrix from the exact supplied clean graph, old matrix,
successor graphs, new pair and adjunction, and encoded irreflexivity. This
constructs neither those witnesses nor a graph collection principle; it does
not prove unconditional quotient congruence or PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccBijectionClosed
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccBijectionPremises
open PASoundness.PAtoCompactSuccCongruenceBijection

/-- The exact new bijection follows in K from the displayed conjunction of
eight supplied premises; all four pointwise cases are actual K derivations. -/
def bijection_closed : KDerivation (imp premisesCode newBijection.encode) :=
  bijection_from_cases PAtoCompactSuccLeftOldPremises.old_from_premises
    PAtoCompactSuccBijectionLeftClosed.top_from_premises
    PAtoCompactSuccBijectionRightClosed.old_from_premises
    PAtoCompactSuccBijectionRightTopCompose.top_from_premises

theorem bijection_closed_certificate : theoremCode (certificate bijection_closed) =
    imp premisesCode newBijection.encode := certificate_correct bijection_closed

end PASoundness.PAtoCompactSuccBijectionClosed

#print axioms PASoundness.PAtoCompactSuccBijectionClosed.bijection_closed
#print axioms PASoundness.PAtoCompactSuccBijectionClosed.bijection_closed_certificate
