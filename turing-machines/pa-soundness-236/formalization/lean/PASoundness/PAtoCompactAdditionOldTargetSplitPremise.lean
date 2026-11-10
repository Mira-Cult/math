import PASoundness.PAtoCompactAdditionOldTargetUniform
import PASoundness.PAtoCompactAdditionSuccessorEdgeSplitUnique

/-! A uniform edge-split premise for the old-target addition case. The
old/new graph adjunction and the top-pair property remain explicit K
antecedents. No graph existence, addition totality or PA bridge is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionOldTargetSplitPremise
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactAdditionOldTargetUniform
open PASoundness.PAtoCompactAdditionSuccessorEdgeSplitUnique
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def hbase : KDerivation (edgeSplitBody 31 32 2 3).encode := by
  simpa [edgeSplitBody,namedAdjoin,namedEither,namedBoth,Formula.encode,
    adjoinCode,CompactProof.both,CompactProof.neg,CompactDerivations.either] using edge_split_23

private def h29 : KDerivation (edgeSplitBody 31 32 29 3).encode := by
  have h := universalInstance 2 29 (edgeSplitBody 31 32 2 3) (by decide) (by decide) (by decide)
  have hc := KDerivation.mp (.generalize 2 hbase) h
  have hr : replace 2 29 (edgeSplitBody 31 32 2 3) = edgeSplitBody 31 32 29 3 := by decide
  rw [hr] at hc
  exact hc

private def h2928 : KDerivation (edgeSplitBody 31 32 29 28).encode := by
  have h := universalInstance 3 28 (edgeSplitBody 31 32 29 3) (by decide) (by decide) (by decide)
  have hc := KDerivation.mp (.generalize 3 h29) h
  have hr : replace 3 28 (edgeSplitBody 31 32 29 3) = edgeSplitBody 31 32 29 28 := by decide
  rw [hr] at hc
  exact hc

/-- The supplied graph adjunction and unequal-label pair yield the literal
uniform old-or-new edge split at target 28. -/
def split_from_graph_pair : KDerivation (imp (adjoinCode 6 11 9 16)
    (imp (pairFormula 11 31 32).encode splitUniform.encode)) := by
  let A := adjoinCode 6 11 9 16
  let P := (pairFormula 11 31 32).encode
  let B : Formula := .imp (graphFormula 9 29 28)
    (namedEither (graphFormula 6 29 28) (namedBoth (.equal 29 31) (.equal 28 32)))
  let Γ := [P,A]
  have hp : Context Γ P := .head _ _
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hstep : KDerivation (imp A (imp P B.encode)) := by
    simpa [edgeSplitBody,B,A,P,namedAdjoin,namedEither,namedBoth,Formula.encode,
      adjoinCode,CompactProof.both,CompactProof.neg,CompactDerivations.either] using h2928
  have hb : Context Γ B.encode := .mp hp (.mp ha (.closed hstep))
  have hvA : KDerivation (imp A (allCode 29 A)) := by
    have h := (namedAdjoin 6 11 9 16).vacuity 29 (by decide)
    simpa [A,namedAdjoin,namedBoth,namedEither,adjoinCode,Formula.encode,
      CompactProof.both,CompactProof.neg,CompactDerivations.either] using h
  have hvP : KDerivation (imp P (allCode 29 P)) := (pairFormula 11 31 32).vacuity 29 (by decide)
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 29 z)) := by
    intro z hz
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hz
    by_cases h : z = P
    · subst z; exact hvP
    · have h' : z = A := hz.resolve_left h
      subst z; exact hvA
  have hout : Context Γ splitUniform.encode := Context.generalize 29 hv hb
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hout

theorem split_from_graph_pair_certificate : theoremCode (certificate split_from_graph_pair) =
    imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode splitUniform.encode) :=
  certificate_correct split_from_graph_pair
end PASoundness.PAtoCompactAdditionOldTargetSplitPremise
#print axioms PASoundness.PAtoCompactAdditionOldTargetSplitPremise.split_from_graph_pair
#print axioms PASoundness.PAtoCompactAdditionOldTargetSplitPremise.split_from_graph_pair_certificate
