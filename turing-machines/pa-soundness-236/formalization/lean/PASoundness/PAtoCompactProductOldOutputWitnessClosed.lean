import PASoundness.PAtoCompactProductOldOutputWitnessFromReflection
import PASoundness.PAtoCompactProductFullPrefixOldTripleReflection
import PASoundness.PAtoCompactFreeVacuity

/-! The old-output branch of the proposed product reverse clause. It combines
old preimage construction with the full-prefix competitor reflection, keeping
all graph-cleanliness, inclusion, successor and old-reverse hypotheses
explicit. The suffix-output branch, full product matrix and multiplication
totality are not proved here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOldOutputWitnessClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactProductOldOutputPreimage
open PASoundness.PAtoCompactProductOldOutputWitnessFromReflection
open PASoundness.PAtoCompactProductOldReverseUniqueTransfer
open PASoundness.PAtoCompactProductTripleReflectionLift
open PASoundness.PAtoCompactProductFullPrefixOldTripleReflection
open PASoundness.PAtoCompactProductOldSuffixExclusion
open PASoundness.PAtoCompactProductOldCompetitorEndpoints
open PASoundness.PAtoCompactMultiplicationFullPrefixOldEdge
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
open PASoundness.PAtoCompactFilterInstantiation
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def inclusion : Formula := .all 9 (.imp (.member 10 9) (.member 64 9))
private def guard : Formula := namedBoth hypotheses oldClean
private def filterF : Formula := .all 35 (namedFilterBody 45 40 35 (Formula.member 32 35).not)

private theorem oldTriple : triple 10 = competitorTriple 10 := by decide
private theorem newTriple : triple 64 = competitorTriple 64 := by decide

private def reflected : KDerivation (imp guard.encode (imp (member 38 7) (imp (member 31 8)
    (imp (competitorTriple 64).encode
      (both (member 30 7) (competitorTriple 10).encode))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(competitorTriple 64).encode, member 31 8, member 38 7, guard.encode]
  have ht : Context Γ (competitorTriple 64).encode := .head _ _
  have hg : Context Γ guard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both hypotheses.encode oldClean.encode) := by
    simpa [guard,namedBoth,Formula.not,Formula.encode,both,neg] using hg
  have hh := Context.conjunctionLeft hg'
  have hc := Context.conjunctionRight hg'
  have ht' : Context Γ (triple 64).encode := by simpa only [newTriple] using ht
  have hp : Context Γ (both (triple 10).encode competitorEndpoints.encode) :=
    .mp ht' (.mp hc (.mp hh (.closed old_output_triple_endpoints)))
  have he : Context Γ (both (member 30 7) (both (member 31 8) (member 32 5))) := by
    have h := Context.conjunctionRight hp
    simpa [competitorEndpoints,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have ho : Context Γ (competitorTriple 10).encode := by
    simpa only [oldTriple] using (Context.conjunctionLeft hp)
  exact Context.conjunctionIntro (Context.conjunctionLeft he) ho

/-- Under full-prefix no-garbage, clean old and suffix graphs, the literal
suffix filter, graph inclusion, a source successor and the old reverse clause,
the old-output preimage is unique against all new-graph competitors. The old
output membership is already part of `hypotheses`. -/
def old_output_unique : KDerivation (imp hypotheses.encode (imp oldClean.encode
    (imp inclusion.encode (imp (successorCode 30 38 39)
      (imp oldReverse.encode targetWitness.encode))))) := by
  have h3 : KDerivation (imp guard.encode (allCode 3 guard.encode)) :=
    free_vacuity 3 guard (by decide)
  have h4 : KDerivation (imp guard.encode (allCode 4 guard.encode)) :=
    free_vacuity 4 guard (by decide)
  have h7 : KDerivation (imp guard.encode (allCode 7 guard.encode)) :=
    free_vacuity 7 guard (by decide)
  have h8 : KDerivation (imp guard.encode (allCode 8 guard.encode)) :=
    free_vacuity 8 guard (by decide)
  have h := old_output_unique_from_reflection guard h3 h4 h7 h8 reflected
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldReverse.encode,successorCode 30 38 39,inclusion.encode,oldClean.encode,hypotheses.encode]
  have hr : Context Γ oldReverse.encode := .head _ _
  have hs : Context Γ (successorCode 30 38 39) := .hypothesis (by simp [Γ])
  have hi : Context Γ inclusion.encode := .hypothesis (by simp [Γ])
  have hc : Context Γ oldClean.encode := .hypothesis (by simp [Γ])
  have hh : Context Γ hypotheses.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ guard.encode := by
    simpa [guard,namedBoth,Formula.not,Formula.encode,both,neg] using Context.conjunctionIntro hh hc
  have hp : Context Γ (both fullNoGarbage.encode (both suffixClean.encode
      (both filterF.encode (member 32 5)))) := by
    change Context Γ (both fullNoGarbage.encode (both suffixClean.encode
      (both filterF.encode (member 32 5)))) at hh
    exact hh
  have hm : Context Γ (member 32 5) := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hp))
  exact .mp hm (.mp hr (.mp hs (.mp hi (.mp hg (.closed h)))))

theorem old_output_unique_certificate : theoremCode (certificate old_output_unique) =
    imp hypotheses.encode (imp oldClean.encode (imp inclusion.encode
      (imp (successorCode 30 38 39) (imp oldReverse.encode targetWitness.encode)))) :=
  certificate_correct old_output_unique
end PASoundness.PAtoCompactProductOldOutputWitnessClosed
#print axioms PASoundness.PAtoCompactProductOldOutputWitnessClosed.old_output_unique
#print axioms PASoundness.PAtoCompactProductOldOutputWitnessClosed.old_output_unique_certificate
