import PASoundness.PAtoCompactSuccCongruenceWitnessExists
import PASoundness.PAtoCompactOrderIsomorphism

/-! The proposed addition-successor graph extension can choose the ordered
pair (31,32), then adjoin that same pair object to graph 6. These are local
K witness constructions, not arbitrary graph collection, the complete
isomorphism extension, or PA proof translation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorPairGraphExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactKuratowskiAnyNames PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.PAtoCompactSuccCongruenceWitnessExists
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- K constructs an ordered pair of the unequal syntactic endpoint names. -/
def addition_top_pair_exists : KDerivation (existsCode 11 (pairFormula 11 31 32).encode) :=
  pair_exists_with_names 31 32 11 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- Under one pair witness at 11, K constructs a new graph at 9 by adjoining
that very pair object to the old graph at 6. -/
def addition_pair_graph_exists : KDerivation (existsCode 11
    (both (pairFormula 11 31 32).encode (existsCode 9 (adjoinCode 6 11 9 16)))) := by
  have ha : KDerivation (existsCode 9 (adjoinCode 6 11 9 16)) := by
    simpa [newGraph] using adjoin_exists
  have hstep : KDerivation (imp (pairFormula 11 31 32).encode
      (both (pairFormula 11 31 32).encode (existsCode 9 (adjoinCode 6 11 9 16)))) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.conjunctionIntro (.head _ _) (.closed ha)
  exact .mp addition_top_pair_exists (existsCongr 11 hstep)

theorem addition_top_pair_exists_certificate : theoremCode (certificate addition_top_pair_exists) =
    existsCode 11 (pairFormula 11 31 32).encode := certificate_correct addition_top_pair_exists

theorem addition_pair_graph_exists_certificate : theoremCode (certificate addition_pair_graph_exists) =
    existsCode 11 (both (pairFormula 11 31 32).encode (existsCode 9 (adjoinCode 6 11 9 16))) :=
  certificate_correct addition_pair_graph_exists
end PASoundness.PAtoCompactAdditionSuccessorPairGraphExists
#print axioms PASoundness.PAtoCompactAdditionSuccessorPairGraphExists.addition_top_pair_exists
#print axioms PASoundness.PAtoCompactAdditionSuccessorPairGraphExists.addition_top_pair_exists_certificate
#print axioms PASoundness.PAtoCompactAdditionSuccessorPairGraphExists.addition_pair_graph_exists
#print axioms PASoundness.PAtoCompactAdditionSuccessorPairGraphExists.addition_pair_graph_exists_certificate
