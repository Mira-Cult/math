import PASoundness.PAtoCompactMultiplicationFourCaseLex
import PASoundness.PAtoCompactMultiplicationLexSharedContext
import PASoundness.PAtoCompactProductCleanEndpointsSecond
import PASoundness.PAtoCompactMultiplicationOldLexActual

/-! Actual old/old point case for the multiplication lex assembler. The
shared context supplies both the old product matrix and the separately
specified clean graph. Both actual old triple branches remain explicit; no
raw matrix is treated as a graph-cleanliness theorem. This does not establish
row collection, the complete lex matrix, multiplication totality, or PA
soundness. -/
namespace PASoundness.PAtoCompactMultiplicationOldOldCaseClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactMultiplicationLexSharedContext
open PASoundness.PAtoCompactMultiplicationFourCaseLex
open PASoundness.PAtoCompactMultiplicationOldLexActual
open PASoundness.PAtoCompactProductCleanEndpointsRelocated
open PASoundness.PAtoCompactProductCleanEndpointsSecond
open PASoundness.PAtoCompactProductCleanLexTransfer
open PASoundness.PAtoCompactMultiplicationSameRowLex
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The exact shared context and two old-graph triples yield both literal
lexicographic comparisons, after extracting all six old endpoints from the
explicit clean-graph condition. -/
def old_old_case : KDerivation (imp sharedPremise.encode
    (imp oldFirst (imp oldSecond comparisons))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldSecond,oldFirst,sharedPremise.encode]
  have h2 : Context Γ oldSecond := .head _ _
  have h1 : Context Γ oldFirst := .hypothesis (by simp [Γ])
  have hp : Context Γ sharedPremise.encode := .hypothesis (by simp [Γ])
  have hp' : Context Γ (both oldMatrixActual.encode
      (both PAtoCompactMultiplicationLexSharedContext.oldCleanActual.encode
        (both (domainAt 100 45).encode (both (domainAt 100 32).encode
          (both (domainAt 100 30).encode (both cutAlternative.encode
            (both suffixFilter.encode (both PAtoCompactMultiplicationNewRowSuffixOrder.suffixOrder.encode
              PAtoCompactMultiplicationSuffixCleanEdges.suffixClean.encode)))))))) := by
    simpa [sharedPremise,namedBoth,Formula.not,Formula.encode,both,neg] using hp
  have hm : Context Γ oldMatrixActual.encode := Context.conjunctionLeft hp'
  have hc : Context Γ PAtoCompactProductCleanEndpointsRelocated.oldCleanActual.encode := by
    have h := Context.conjunctionLeft (Context.conjunctionRight hp')
    simpa [PAtoCompactMultiplicationLexSharedContext.oldCleanActual,
      PAtoCompactProductCleanEndpointsRelocated.oldCleanActual,
      PAtoCompactProductCleanTripleEndpoints.oldClean] using h
  have htr1 : Context Γ PASoundness.PAtoCompactOldTripleEdgeExtract.oldTriple.encode := by
    simpa [oldFirst, PASoundness.PAtoCompactOldTripleEdgeExtract.oldTriple,
      PASoundness.PAtoCompactMultiplicationOldTripleIntro.oldTriple] using h1
  have htr2 : Context Γ secondTriple.encode := by
    simpa [oldSecond,secondTriple,PAtoCompactMultiplicationSecondBranchSplit.old_triple_shape] using h2
  have he1 : Context Γ (both (member 30 3) (both (member 31 4) (member 32 5))) := by
    have h := Context.mp htr1 (Context.mp hc (.closed first_endpoints))
    simpa [firstEndpoints,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have he2 : Context Γ (both (member 30 7) (both (member 31 8) (member 32 9))) := by
    have h := Context.mp htr2 (Context.mp hc (.closed second_endpoints))
    simpa [secondEndpoints,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have htr1' : Context Γ (tripleAt 10 3 4 5).encode := by
    simpa [oldFirst,tripleAt,PASoundness.PAtoCompactMultiplicationOldTripleIntro.oldTriple] using h1
  have htr2' : Context Γ (tripleAt 10 7 8 9).encode := by
    simpa [oldSecond,tripleAt,PAtoCompactMultiplicationSecondBranchSplit.old_triple_shape] using h2
  have ha : Context Γ oldAntecedent.encode := by
    have h := Context.conjunctionIntro (Context.conjunctionLeft he1)
      (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight he1))
        (Context.conjunctionIntro (Context.conjunctionRight (Context.conjunctionRight he1))
          (Context.conjunctionIntro (Context.conjunctionLeft he2)
            (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight he2))
              (Context.conjunctionIntro (Context.conjunctionRight (Context.conjunctionRight he2))
                (Context.conjunctionIntro htr1' htr2'))))))
    simpa [oldAntecedent,namedBoth,Formula.not,Formula.encode,both,neg] using h
  simpa [comparisons] using (Context.mp ha (Context.mp hm (.closed old_old_actual)))

theorem old_old_case_certificate : theoremCode (certificate old_old_case) =
    imp sharedPremise.encode (imp oldFirst (imp oldSecond comparisons)) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationOldOldCaseClosed
#print axioms PASoundness.PAtoCompactMultiplicationOldOldCaseClosed.old_old_case
#print axioms PASoundness.PAtoCompactMultiplicationOldOldCaseClosed.old_old_case_certificate
