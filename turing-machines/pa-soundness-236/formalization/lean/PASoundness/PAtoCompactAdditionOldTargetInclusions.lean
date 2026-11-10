import PASoundness.PAtoCompactAdditionOldTargetWitnessTransfer
import PASoundness.PAtoCompactTransitiveClosure
import PASoundness.PAtoCompactSuccCongruenceEdgeCoverage
import PASoundness.PAtoCompactPartialInverseOldEdge

/-! Explicit finite K proofs of the source-domain and old-graph inclusions
needed by the distinct-top old-target witness transfer. These are conditional
on the supplied successor and graph-adjunction formulas; they do not establish
a full bijection, arithmetic totality or PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionOldTargetInclusions
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccCongruenceEdgeCoverage
open PASoundness.PAtoCompactPartialInverseOldEdge PASoundness.PAtoCompactAdditionOldTargetWitnessTransfer
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A source successor includes every member of the old source. -/
def source_inclusion_from_successor : KDerivation
    (imp (successorCode 31 38 39) sourceInclusion.encode) := by
  let S := successorCode 31 38 39
  let F : Formula := .imp (.member 31 29) (.member 38 29)
  have hpoint : KDerivation (imp S F.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [member 31 29,S]
    have hm : Context Γ (member 31 29) := Context.head _ _
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have he : Context Γ (either (equal 29 31) (member 31 29)) :=
      Context.disjunctionRight (a := equal 29 31) hm
    exact .mp he (.mp hs (.closed (successor_include 31 38 39 29 (by decide) (by decide) (by decide))))
  have hv : KDerivation (imp S (allCode 29 S)) :=
    successor_vacuity 31 38 39 29 (by decide) (by decide) (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  have hs : Context [S] S := Context.head [] _
  have hp : Context [S] F.encode := .mp hs (.closed hpoint)
  exact Context.generalize 29 (by
    intro z hz
    have he : z = S := by simpa using hz
    subst z
    exact hv) hp

/-- Adjoining a pair object preserves every old graph edge at target 28. -/
def graph_inclusion_from_adjoin : KDerivation
    (imp (adjoinCode 6 11 9 16) graphInclusion.encode) := by
  let A := adjoinCode 6 11 9 16
  let F : Formula := .imp (graphFormula 6 29 28) (graphFormula 9 29 28)
  have hp : KDerivation (imp A F.encode) := by
    exact compose old_inclusion (graph_edge_monotone 6 9 29 28)
  have hv : KDerivation (imp A (allCode 29 A)) := by
    have h := (namedAdjoin 6 11 9 16).vacuity 29 (by decide)
    simpa [A,namedAdjoin,namedBoth,namedEither,adjoinCode,Formula.encode,
      CompactProof.both,CompactProof.neg,CompactDerivations.either] using h
  apply Context.closeEmpty
  apply Context.deduction
  have ha : Context [A] A := Context.head [] _
  have hf : Context [A] F.encode := .mp ha (.closed hp)
  exact Context.generalize 29 (by
    intro z hz
    have he : z = A := by simpa using hz
    subst z
    exact hv) hf

theorem source_inclusion_from_successor_certificate :
    theoremCode (certificate source_inclusion_from_successor) =
      imp (successorCode 31 38 39) sourceInclusion.encode :=
  certificate_correct source_inclusion_from_successor

theorem graph_inclusion_from_adjoin_certificate :
    theoremCode (certificate graph_inclusion_from_adjoin) =
      imp (adjoinCode 6 11 9 16) graphInclusion.encode :=
  certificate_correct graph_inclusion_from_adjoin
end PASoundness.PAtoCompactAdditionOldTargetInclusions
#print axioms PASoundness.PAtoCompactAdditionOldTargetInclusions.source_inclusion_from_successor
#print axioms PASoundness.PAtoCompactAdditionOldTargetInclusions.graph_inclusion_from_adjoin
#print axioms PASoundness.PAtoCompactAdditionOldTargetInclusions.source_inclusion_from_successor_certificate
#print axioms PASoundness.PAtoCompactAdditionOldTargetInclusions.graph_inclusion_from_adjoin_certificate
