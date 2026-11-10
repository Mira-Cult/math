import PASoundness.PAtoCompactMultiplicationFourCaseLex
import PASoundness.PAtoCompactMultiplicationLexSharedContext
import PASoundness.PAtoCompactMultiplicationOldOldCaseClosed
import PASoundness.PAtoCompactMultiplicationOldNewCaseClosed
import PASoundness.PAtoCompactMultiplicationNewOldCaseClosed
import PASoundness.PAtoCompactMultiplicationNewNewCaseClosed

/-! Concrete finite-K pointwise lexicographic comparison after splitting two
actual queried graph64 triples. The shared context, including both clean
old/suffix graph hypotheses, and the prefix0 no-garbage invariant remain
literal object-level premises. No extra K proof-data cases are required.
This does not prove row collection, the quantified lex clause, multiplication
totality, or PA soundness. -/
namespace PASoundness.PAtoCompactMultiplicationFourCaseLexClosed
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactMultiplicationLexSharedContext
open PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha
open PASoundness.PAtoCompactMultiplicationFourCaseLex
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- All four branches are discharged by the actual finite K case proofs. -/
def actualCases : CaseProofs sharedPremise.encode where
  oldOld := PAtoCompactMultiplicationOldOldCaseClosed.old_old_case
  oldNew := PAtoCompactMultiplicationOldNewCaseClosed.old_new_case
  newOld := PAtoCompactMultiplicationNewOldCaseClosed.new_old_case
  newNew := PAtoCompactMultiplicationNewNewCaseClosed.new_new_case

/-- The two actual queried graph triples obey both lexicographic comparisons
under the explicit shared context and no-garbage hypothesis. -/
def point_lex : KDerivation (imp sharedPremise.encode (imp (noGarbage 64).encode
    (imp queriedTriple.encode
      (imp (PAtoCompactMultiplicationSecondBranchSplit.tripleAt 64).encode comparisons)))) :=
  point_of_cases sharedPremise.encode actualCases

theorem point_lex_certificate : theoremCode (certificate point_lex) =
    imp sharedPremise.encode (imp (noGarbage 64).encode (imp queriedTriple.encode
      (imp (PAtoCompactMultiplicationSecondBranchSplit.tripleAt 64).encode comparisons))) :=
  certificate_correct _
end PASoundness.PAtoCompactMultiplicationFourCaseLexClosed
#print axioms PASoundness.PAtoCompactMultiplicationFourCaseLexClosed.actualCases
#print axioms PASoundness.PAtoCompactMultiplicationFourCaseLexClosed.point_lex
#print axioms PASoundness.PAtoCompactMultiplicationFourCaseLexClosed.point_lex_certificate
