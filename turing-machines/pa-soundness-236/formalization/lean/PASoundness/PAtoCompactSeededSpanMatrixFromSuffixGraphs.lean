import PASoundness.PAtoCompactSeededSpanMatrixWitness
import PASoundness.PAtoCompactSecondSuffixCollectorClause

/-! Supply the seeded collector's two widened forward clauses from the
explicit clean suffix graphs and filters. The remaining hypotheses retain
the graph data, candidate/cut facts and order clauses. -/
namespace PASoundness.PAtoCompactSeededSpanMatrixFromSuffixGraphs

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage PASoundness.PAtoCompactSeededSpanSeedSourceUnique
open PASoundness.PAtoCompactSeededSpanCleanEndpoints PASoundness.PAtoCompactFirstSpanPathOutside
open PASoundness.PAtoCompactFirstSpanTargetOutside PASoundness.PAtoCompactCommonSourceSpanImages

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def guard : Formula := namedBoth (namedCandidate 1) (namedBoth seedBijection
  (namedBoth firstBijection (namedBoth secondBijection
    (namedBoth PASoundness.PAtoCompactSeededSpanMatrixWitness.fixedBase
      (namedBoth PASoundness.PAtoCompactFirstSuffixOrderWiden.suffixOrder
        PASoundness.PAtoCompactSecondSuffixOrderWiden.suffixOrder)))))

/-- A single output graph with the target matrix follows from the stated
clean-suffix graphs; no extra widened collector clauses are assumed. -/
def matrix_from_suffix_graphs : KDerivation (imp guard.encode
    PASoundness.PAtoCompactSeededSpanMatrixWitness.output.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hr := Context.conjunctionRight hg
  have hr := Context.conjunctionRight hr
  have hb1 : Context Γ firstBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hb2 : Context Γ secondBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hbase : Context Γ PASoundness.PAtoCompactSeededSpanMatrixWitness.fixedBase.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hbase
  have hr := Context.conjunctionRight hr
  have hr := Context.conjunctionRight hr
  have hr := Context.conjunctionRight hr
  have hr := Context.conjunctionRight hr
  have hr := Context.conjunctionRight hr
  have hsource : Context Γ outsideGuard.encode := Context.conjunctionLeft hr
  have htarget : Context Γ targetGuard.encode := Context.conjunctionLeft (Context.conjunctionRight hr)
  have hfirst : Context Γ firstClause.encode :=
    .mp hsource (.mp hb1 (.closed PASoundness.PAtoCompactFirstSuffixCollectorClause.first_collector_clause))
  have hsecond : Context Γ secondClause.encode :=
    .mp htarget (.mp hb2 (.closed PASoundness.PAtoCompactSecondSuffixCollectorClause.second_collector_clause))
  have hw : Context Γ PASoundness.PAtoCompactSeededSpanMatrixWitness.guard.encode :=
    Context.conjunctionIntro hfirst (Context.conjunctionIntro hsecond hg)
  exact .mp hw (.closed PASoundness.PAtoCompactSeededSpanMatrixWitness.seeded_matrix_witness)

theorem matrix_from_suffix_graphs_certificate : theoremCode (certificate matrix_from_suffix_graphs) =
    imp guard.encode PASoundness.PAtoCompactSeededSpanMatrixWitness.output.encode :=
  certificate_correct matrix_from_suffix_graphs

end PASoundness.PAtoCompactSeededSpanMatrixFromSuffixGraphs

#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromSuffixGraphs.guard
#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromSuffixGraphs.matrix_from_suffix_graphs
#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromSuffixGraphs.matrix_from_suffix_graphs_certificate
