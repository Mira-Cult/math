import PASoundness.PAtoCompactMultiplicationRowQueryCompetitor

/-! Capture-safe full-prefix specialization of the pointwise multiplication
row query. The free prefix name 0 is replaced by the existing source name 31;
this intentionally aliases those syntactic names and does not assume distinct
values. It is a query lemma, not graph collection or multiplication totality. -/
namespace PASoundness.PAtoCompactMultiplicationRowQueryCompetitorFull
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactMultiplicationRowQueryCompetitor
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def statement : Formula := .imp competitorPairs
  (.imp (replace 9 63 rowWitness) competitorResult)

/-- At the full source prefix, the same edge query gives the fixed major,
source minor and corresponding map edge. The row-witness and graph object
remain the same; no pair-representative uniqueness is used. -/
def row_query_full_prefix : KDerivation (imp competitorPairs.encode
    (imp (replace 9 63 (replace 0 31 rowWitness)).encode competitorResult.encode)) := by
  have h : KDerivation statement.encode := by
    simpa [statement,Formula.encode] using row_query_competitor
  have hi := universalInstance 0 31 statement (by decide) (by decide) (by decide)
  have hs := KDerivation.mp (.generalize 0 h) hi
  have hshape : replace 0 31 statement = .imp competitorPairs
      (.imp (replace 9 63 (replace 0 31 rowWitness)) competitorResult) := by decide
  rw [hshape] at hs
  simpa [Formula.encode] using hs

theorem row_query_full_prefix_certificate : theoremCode (certificate row_query_full_prefix) =
    imp competitorPairs.encode
      (imp (replace 9 63 (replace 0 31 rowWitness)).encode competitorResult.encode) :=
  certificate_correct row_query_full_prefix
end PASoundness.PAtoCompactMultiplicationRowQueryCompetitorFull
#print axioms PASoundness.PAtoCompactMultiplicationRowQueryCompetitorFull.row_query_full_prefix
#print axioms PASoundness.PAtoCompactMultiplicationRowQueryCompetitorFull.row_query_full_prefix_certificate
