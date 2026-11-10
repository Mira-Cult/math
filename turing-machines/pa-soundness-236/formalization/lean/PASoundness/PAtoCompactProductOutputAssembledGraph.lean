import PASoundness.PAtoCompactProductOutputCollectionSource
import PASoundness.PAtoCompactProductOutputForwardClauseAll
import PASoundness.PAtoCompactProductOutputReverseClauseAll
import PASoundness.PAtoCompactProductOutputLexGraphAll

/-! Retain one actual output graph with its guarded invariant, forward and
reverse existence/uniqueness clauses and lex comparison. Standard target
product-matrix syntax alignment and term-graph output transport are separate. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputAssembledGraph

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactProductMatchFactorOrderPoint PASoundness.PAtoCompactProductOutputReverseCoverage
open PASoundness.PAtoCompactProductOutputActualPoint PASoundness.PAtoCompactProductOutputCollectionInsideConditional
open PASoundness.PAtoCompactProductOutputCollectionSource PASoundness.PAtoCompactProductOutputForwardClauseAll
open PASoundness.PAtoCompactProductOutputReverseClauseAll PASoundness.PAtoCompactProductOutputLexGraphAll

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def extendedAssumptions : Formula := namedBoth assumptions firstOrder
def assembledGraph : Formula := namedBoth actualInvariant
  (namedBoth forwardClause (namedBoth reverseClause graphOrder))

/-- Assemble all three clauses for the same explicitly supplied graph58. -/
def actual_to_assembled : KDerivation (imp extendedAssumptions.encode
    (imp actualInvariant.encode assembledGraph.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [actualInvariant.encode,extendedAssumptions.encode]
  have hi : Context Γ actualInvariant.encode := .head _ _
  have he : Context Γ extendedAssumptions.encode := .hypothesis (by simp [Γ])
  have he' : Context Γ (both assumptions.encode firstOrder.encode) := by
    simpa [extendedAssumptions, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using he
  have ha := Context.conjunctionLeft he'
  have ho := Context.conjunctionRight he'
  have ha' : Context Γ (both relocatedMatrix.encode PAtoCompactProductMatchFactorImages.firstBijection.encode) := by
    simpa [assumptions, relocatedMatrix, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using ha
  have hf := Context.mp hi (Context.mp ha (.closed forward_clause_all))
  have hr := Context.mp hi (Context.mp ha (.closed reverse_clause_all))
  have hl := Context.mp hi (Context.mp ho (Context.mp (Context.conjunctionLeft ha') (.closed graph_order)))
  simpa [assembledGraph, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
    Context.conjunctionIntro hi (Context.conjunctionIntro hf (Context.conjunctionIntro hr hl))

/-- Construct one graph satisfying all displayed clauses under the source
candidate, source product matrix and output-isomorphism bijection and order. -/
noncomputable def assembled_graph : KDerivation (imp extendedAssumptions.encode
    (imp (candidateCode 0 81 77 78 72 64 73 59 75) (existsCode 58 assembledGraph.encode))) := by
  have hmap := conditionalExistsCongr 58 (free_vacuity 58 extendedAssumptions (by decide)) actual_to_assembled
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [candidateCode 0 81 77 78 72 64 73 59 75,extendedAssumptions.encode]
  have hc : Context Γ (candidateCode 0 81 77 78 72 64 73 59 75) := .head _ _
  have he : Context Γ extendedAssumptions.encode := .hypothesis (by simp [Γ])
  have he' : Context Γ (both assumptions.encode firstOrder.encode) := by
    simpa [extendedAssumptions, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using he
  have hw := Context.mp hc (Context.mp (Context.conjunctionLeft he') (.closed source_collection))
  have hw' : Context Γ (existsCode 58 actualInvariant.encode) := by simpa [actualInvariant] using hw
  exact .mp hw' (.mp he (.closed hmap))

theorem assembled_graph_certificate : theoremCode (certificate assembled_graph) =
    imp extendedAssumptions.encode (imp (candidateCode 0 81 77 78 72 64 73 59 75)
      (existsCode 58 assembledGraph.encode)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputAssembledGraph

#print axioms PASoundness.PAtoCompactProductOutputAssembledGraph.actual_to_assembled
#print axioms PASoundness.PAtoCompactProductOutputAssembledGraph.assembled_graph
#print axioms PASoundness.PAtoCompactProductOutputAssembledGraph.assembled_graph_certificate
