import PASoundness.PAtoCompactSuccCongruenceData
import PASoundness.PAtoCompactTransitiveClosure

/-! Capture-safe K vacuity at pointwise source name 2 for the explicitly
supplied successor-congruence hypotheses. No hypothesis is asserted here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccPremiseVacuity
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactPointAdjoin
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def clean_vacuity : KDerivation (imp cleanGraph (allCode 2 cleanGraph)) := by
  let f : Formula := .all 19 (.imp (.member 6 19) (edgePredicate 19 0 1))
  have h := f.vacuity 2 (by decide)
  simpa [f, cleanGraph, Formula.encode] using h

def source_successor_vacuity : KDerivation (imp sourceSuccessor (allCode 2 sourceSuccessor)) :=
  successor_vacuity 0 7 14 2 (by decide) (by decide) (by decide)

def target_successor_vacuity : KDerivation (imp targetSuccessor (allCode 2 targetSuccessor)) :=
  successor_vacuity 1 8 15 2 (by decide) (by decide) (by decide)

def pair_vacuity : KDerivation (imp newPair (allCode 2 newPair)) :=
  (pairFormula 11 0 1).vacuity 2 (by decide)

def graph_vacuity : KDerivation (imp newGraph (allCode 2 newGraph)) := by
  let f := namedAdjoin 6 11 9 16
  have h := f.vacuity 2 (by decide)
  simpa [f, namedAdjoin, newGraph, adjoinCode, namedBoth, namedEither,
    Formula.encode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using h

def source_irreflexive_vacuity : KDerivation
    (imp sourceIrreflexive (allCode 2 sourceIrreflexive)) :=
  negationVacuity 2 (membershipVacuity 0 0 2 (by decide) (by decide))

def target_irreflexive_vacuity : KDerivation
    (imp targetIrreflexive (allCode 2 targetIrreflexive)) :=
  negationVacuity 2 (membershipVacuity 1 1 2 (by decide) (by decide))

end PASoundness.PAtoCompactSuccPremiseVacuity

#print axioms PASoundness.PAtoCompactSuccPremiseVacuity.clean_vacuity
#print axioms PASoundness.PAtoCompactSuccPremiseVacuity.source_successor_vacuity
#print axioms PASoundness.PAtoCompactSuccPremiseVacuity.target_successor_vacuity
#print axioms PASoundness.PAtoCompactSuccPremiseVacuity.pair_vacuity
#print axioms PASoundness.PAtoCompactSuccPremiseVacuity.graph_vacuity
#print axioms PASoundness.PAtoCompactSuccPremiseVacuity.source_irreflexive_vacuity
#print axioms PASoundness.PAtoCompactSuccPremiseVacuity.target_irreflexive_vacuity
