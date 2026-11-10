import PASoundness.PAtoCompactSuccCongruenceData
import PASoundness.PAtoCompactKuratowskiAnyNames

/-! The pair and one-point-adjunction witnesses used by the supplied-clean-
graph successor-matrix proof exist in literal K. These are local witness
constructions, not arbitrary graph collection or quotient congruence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccCongruenceWitnessExists
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactKuratowskiAnyNames PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactPointAdjoinSelector
open PASoundness.PAtoCompactSuccCongruenceData

/-- Every assignment to endpoint names 0 and 1 has a represented pair under
existential output name 11. The exact pair formula binds names 20–22. -/
def pair_exists : KDerivation (existsCode 11 newPair) := by
  exact pair_exists_with_names 0 1 11 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- Given the existing graph at 6 and chosen point at 11, K constructs a
one-point adjunction under output name 9 and test binder 16. The exact
predicate code is distinct from all the named binders used by selector 8. -/
def adjoin_exists : KDerivation (existsCode 9 newGraph) := by
  have hlarge := (PAtoCompactPointAdjoinSelector.predicate_names_lt 6 11 17).2.2
  exact adjoin_graph_exists_fresh 6 11 17 16 9
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by omega) (by decide) (by decide) (by decide) (by decide) (by omega)

theorem pair_exists_certificate : theoremCode (certificate pair_exists) =
    existsCode 11 newPair := certificate_correct pair_exists

theorem adjoin_exists_certificate : theoremCode (certificate adjoin_exists) =
    existsCode 9 newGraph := certificate_correct adjoin_exists

end PASoundness.PAtoCompactSuccCongruenceWitnessExists

#print axioms PASoundness.PAtoCompactSuccCongruenceWitnessExists.pair_exists
#print axioms PASoundness.PAtoCompactSuccCongruenceWitnessExists.adjoin_exists
#print axioms PASoundness.PAtoCompactSuccCongruenceWitnessExists.pair_exists_certificate
#print axioms PASoundness.PAtoCompactSuccCongruenceWitnessExists.adjoin_exists_certificate
