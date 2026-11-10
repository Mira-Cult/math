import PASoundness.PAtoCompactAdditionTopEdgeCases
import PASoundness.PAtoCompactAdditionSuccessorGraphTop

/-! Top-source and top-target witnesses for the unequal-endpoint addition
graph. These two bijection cases retain explicit graph and adjunction
hypotheses; they do not prove full bijection, addition totality, or PA soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionTopWitnessUnequal
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.PAtoCompactSuccTopWitness PASoundness.PAtoCompactAdditionSuccessorGraphTop
open PASoundness.PAtoCompactAdditionSuccessorGraphClean PASoundness.PAtoCompactAdditionTopEdgeCases
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The explicitly adjoined old result belongs to the new suffix. -/
def added_target_member : KDerivation (imp (adjoinCode 34 32 40 41) (member 40 32)) := by
  let f := namedBoth (.imp (.member 40 41) (namedEither (.equal 41 32) (.member 34 41)))
    (.imp (namedEither (.equal 41 32) (.member 34 41)) (.member 40 41))
  have hi := universalInstance 41 32 f (by decide) (by decide) (by decide)
  have hi' : KDerivation (imp (adjoinCode 34 32 40 41)
      (both (imp (member 40 32) (either (equal 32 32) (member 34 32)))
        (imp (either (equal 32 32) (member 34 32)) (member 40 32)))) := by
    simpa [f,adjoinCode,namedBoth,namedEither,Formula.encode,replace,rename,both,neg,either] using hi
  apply Context.closeEmpty
  apply Context.deduction
  have hh : Context [adjoinCode 34 32 40 41] (adjoinCode 34 32 40 41) := .head _ _
  have hrow := Context.mp hh (.closed hi')
  have he : Context [adjoinCode 34 32 40 41] (either (equal 32 32) (member 34 32)) :=
    Context.disjunctionLeft (.closed (equalityReflexive 32))
  exact .mp he (Context.conjunctionRight hrow)

/-- A target in the new suffix carrying the top source, unique among all
new graph edges with that source. -/
def topSourceWitness : Formula := namedBoth (.member 40 3)
  (namedBoth (graphFormula 9 31 3)
    (.all 4 (.imp (graphFormula 9 31 4) (.equal 4 3))))
private def witness32 : Formula := namedBoth (.member 40 32)
  (namedBoth (graphFormula 9 31 32)
    (.all 4 (.imp (graphFormula 9 31 4) (.equal 4 32))))

/-- The new source's witness exists under the supplied pair, clean graph,
new-graph adjunction, and new-suffix adjunction. -/
def top_source_witness : KDerivation (imp (adjoinCode 34 32 40 41)
    (imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode
      (imp oldClean.encode (existsCode 3 topSourceWitness.encode))))) := by
  have hIntro := exists_variable_intro 3 32 topSourceWitness (by decide) (by decide) (by decide)
  have hSyntax : replace 3 32 topSourceWitness = witness32 := by decide
  rw [hSyntax] at hIntro
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldClean.encode,(pairFormula 11 31 32).encode,
    adjoinCode 6 11 9 16,adjoinCode 34 32 40 41]
  have hc : Context Γ oldClean.encode := .head _ _
  have hp : Context Γ (pairFormula 11 31 32).encode := .hypothesis (by simp [Γ])
  have hg : Context Γ (adjoinCode 6 11 9 16) := .hypothesis (by simp [Γ])
  have ht : Context Γ (adjoinCode 34 32 40 41) := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 40 32) := .mp ht (.closed added_target_member)
  have hpairmem : Context Γ (member 9 11) := .mp hg (.closed new_graph_contains_pair)
  have htop : Context Γ (graphFormula 9 31 32).encode :=
    .mp (Context.conjunctionIntro hpairmem hp) (.closed top_from_pair)
  have hu : Context Γ (allCode 4 (imp (graphFormula 9 31 4).encode (equal 4 32))) :=
    .mp hc (.mp hp (.mp hg (.closed source_unique_all)))
  have hw : Context Γ witness32.encode := Context.conjunctionIntro hm (Context.conjunctionIntro htop hu)
  exact .mp hw (.closed hIntro)

theorem top_source_witness_certificate : theoremCode (certificate top_source_witness) =
    imp (adjoinCode 34 32 40 41) (imp (adjoinCode 6 11 9 16)
      (imp (pairFormula 11 31 32).encode
        (imp oldClean.encode (existsCode 3 topSourceWitness.encode)))) :=
  certificate_correct top_source_witness

/-- A source in the successor domain carrying the new top target, unique
among all new graph edges with that target. -/
def topTargetWitness : Formula := namedBoth (.member 38 3)
  (namedBoth (graphFormula 9 3 32)
    (.all 4 (.imp (graphFormula 9 4 32) (.equal 4 3))))
private def targetWitness31 : Formula := namedBoth (.member 38 31)
  (namedBoth (graphFormula 9 31 32)
    (.all 4 (.imp (graphFormula 9 4 32) (.equal 4 31))))

/-- The new target's witness exists under the supplied old suffix filter,
source successor, pair, clean graph, and graph adjunction. -/
def top_target_witness : KDerivation (imp suffix (imp (successorCode 31 38 39)
    (imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode
      (imp oldClean.encode (existsCode 3 topTargetWitness.encode)))))) := by
  have hIntro := exists_variable_intro 3 31 topTargetWitness (by decide) (by decide) (by decide)
  have hSyntax : replace 3 31 topTargetWitness = targetWitness31 := by decide
  rw [hSyntax] at hIntro
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldClean.encode,(pairFormula 11 31 32).encode,
    adjoinCode 6 11 9 16,successorCode 31 38 39,suffix]
  have hc : Context Γ oldClean.encode := .head _ _
  have hp : Context Γ (pairFormula 11 31 32).encode := .hypothesis (by simp [Γ])
  have hg : Context Γ (adjoinCode 6 11 9 16) := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode 31 38 39) := .hypothesis (by simp [Γ])
  have hf : Context Γ suffix := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 38 31) :=
    .mp hs (.closed (successor_contains_input 31 38 39 (by decide) (by decide)))
  have hpairmem : Context Γ (member 9 11) := .mp hg (.closed new_graph_contains_pair)
  have htop : Context Γ (graphFormula 9 31 32).encode :=
    .mp (Context.conjunctionIntro hpairmem hp) (.closed top_from_pair)
  have hu : Context Γ (allCode 4 (imp (graphFormula 9 4 32).encode (equal 4 31))) :=
    .mp hc (.mp hp (.mp hg (.mp hf (.closed target_unique_all))))
  have hw : Context Γ targetWitness31.encode := Context.conjunctionIntro hm (Context.conjunctionIntro htop hu)
  exact .mp hw (.closed hIntro)

theorem top_target_witness_certificate : theoremCode (certificate top_target_witness) =
    imp suffix (imp (successorCode 31 38 39) (imp (adjoinCode 6 11 9 16)
      (imp (pairFormula 11 31 32).encode
        (imp oldClean.encode (existsCode 3 topTargetWitness.encode))))) :=
  certificate_correct top_target_witness

end PASoundness.PAtoCompactAdditionTopWitnessUnequal
#print axioms PASoundness.PAtoCompactAdditionTopWitnessUnequal.top_source_witness
#print axioms PASoundness.PAtoCompactAdditionTopWitnessUnequal.top_source_witness_certificate

#print axioms PASoundness.PAtoCompactAdditionTopWitnessUnequal.top_target_witness
#print axioms PASoundness.PAtoCompactAdditionTopWitnessUnequal.top_target_witness_certificate
