import PASoundness.PAtoCompactPartialInverseOldGraphElim
import PASoundness.PAtoCompactPartialInverseWitnessChain

/-! Inside-source successor step with old and new partial-inverse graph,
pair, endpoint alias and image witnesses eliminated. Original bijection,
successor graph and source membership remain explicit K antecedents. This is
not the outside-source branch, a complete induction or inverse existence. -/
namespace PASoundness.PAtoCompactPartialInverseInsideClosed
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPartialInverseBase PASoundness.PAtoCompactPartialInversePairElim
open PASoundness.PAtoCompactPartialInverseOldGraphElim PASoundness.PAtoCompactPartialInverseWitnessChain

/-- If the prefix endpoint is in the original graph's source domain, an
existing partial inverse extends across a supplied successor prefix. -/
def inside_successor_closed : KDerivation
    (imp bijectionFormula.encode (imp (successorCode 8 10 15)
      (imp (member 0 8) (imp (existsCode 7 partialInverse.encode)
        (existsCode 7 nextInvariant.encode))))) :=
  eliminate_old_graph inside_step_with_old_graph

theorem inside_successor_closed_certificate : theoremCode (certificate inside_successor_closed) =
    imp bijectionFormula.encode (imp (successorCode 8 10 15)
      (imp (member 0 8) (imp (existsCode 7 partialInverse.encode)
        (existsCode 7 nextInvariant.encode)))) :=
  certificate_correct inside_successor_closed

end PASoundness.PAtoCompactPartialInverseInsideClosed

#print axioms PASoundness.PAtoCompactPartialInverseInsideClosed.inside_successor_closed
#print axioms PASoundness.PAtoCompactPartialInverseInsideClosed.inside_successor_closed_certificate
