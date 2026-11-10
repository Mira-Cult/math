import PASoundness.PAtoCompactPartialInverseSuppliedStep
import PASoundness.PAtoCompactPartialInversePairElim

/-! Construct and eliminate the pair and point-adjoined graph for the inside-
source successor step. The alias, image witness, prefix-successor graph, and
old partial inverse remain explicit. This is not yet full inside-source witness
elimination, induction, inverse existence or quotient symmetry. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseInsideWitness
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactPartialInverseBase
open PASoundness.PAtoCompactPartialInverseImageWitness PASoundness.PAtoCompactPartialInverseCoverageAll
open PASoundness.PAtoCompactPartialInverseCombine PASoundness.PAtoCompactPartialInverseSuppliedStep
open PASoundness.PAtoCompactPartialInversePairElim
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

def retained : Formula := conj (imageBody 12 13) (conj (.equal 12 8)
  (conj (namedSuccessor 8 10 15) partialInverse))

theorem retained_fresh_9 : 9 ∉ retained.names := by decide
theorem retained_fresh_11 : 11 ∉ retained.names := by decide

theorem next_rename_alignment : newPartial = nextInvariant9 := by decide

/-- Reorder the supplied-step premises into the exact curried interface
required for pair and graph witness construction. -/
def curried_step : KDerivation
    (imp retained.encode (imp (pairFormula 11 13 12).encode
      (imp (adjoinCode 7 11 9 14) nextInvariant9.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [adjoinCode 7 11 9 14,(pairFormula 11 13 12).encode,retained.encode]
  have ha : Context Γ (adjoinCode 7 11 9 14) := Context.head _ _
  have hp : Context Γ (pairFormula 11 13 12).encode := .hypothesis (by simp [Γ])
  have hr : Context Γ retained.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ suppliedPremises.encode :=
    Context.conjunctionIntro ha (Context.conjunctionIntro hp hr)
  have hn : Context Γ newPartial.encode := .mp hs (.closed supplied_step)
  rw [← next_rename_alignment]
  exact hn

/-- K constructs some next graph satisfying the successor-prefix invariant,
conditional on a retained image witness, explicit endpoint alias, successor
graph and old invariant. Both pair point 11 and new graph 9 are eliminated;
the resulting graph existential uses the canonical name 7. -/
def pair_and_graph_eliminated : KDerivation
    (imp retained.encode (existsCode 7 nextInvariant.encode)) :=
  eliminate_pair_and_graph retained retained_fresh_9 retained_fresh_11 curried_step

theorem pair_and_graph_eliminated_certificate :
    theoremCode (certificate pair_and_graph_eliminated) =
      imp retained.encode (existsCode 7 nextInvariant.encode) :=
  certificate_correct pair_and_graph_eliminated

end PASoundness.PAtoCompactPartialInverseInsideWitness

#print axioms PASoundness.PAtoCompactPartialInverseInsideWitness.pair_and_graph_eliminated
#print axioms PASoundness.PAtoCompactPartialInverseInsideWitness.pair_and_graph_eliminated_certificate
