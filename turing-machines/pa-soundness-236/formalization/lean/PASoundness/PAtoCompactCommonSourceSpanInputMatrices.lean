import PASoundness.PAtoCompactCommonSourceSpanInduction
import PASoundness.PAtoCompactOrdinalAddition

/-! Extract the two forward clauses from concrete supplied isomorphism
matrices over a common candidate source. Both original graph witnesses remain
explicit, and the common-source span graph is constructed by the separately
drafted induction. No conclusion here establishes the span graph's own
bijection or order matrix. -/
namespace PASoundness.PAtoCompactCommonSourceSpanInputMatrices

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactCommonSourceSpanBase PASoundness.PAtoCompactCommonSourceSpanImages
open PASoundness.PAtoCompactCommonSourceSpanInduction

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Graph 6 is an isomorphism from common input 1 to the first image 0.
The temporary 25 prevents collapsing the two free inputs while swapping. -/
def firstBijection : Formula := replace 25 1 (replace 1 0 (replace 0 25 bijectionFormula))
def firstOrder : Formula := replace 25 1 (replace 1 0 (replace 0 25 orderFormula))
def firstMatrix : Formula := namedBoth firstBijection firstOrder

/-- Graph 7 is an isomorphism from common input 1 to the second image 8. -/
def secondBijection : Formula := replace 6 7 (replace 0 1 (replace 1 8 bijectionFormula))
def secondOrder : Formula := replace 6 7 (replace 0 1 (replace 1 8 orderFormula))
def secondMatrix : Formula := namedBoth secondBijection secondOrder

private def firstBackClause : Formula := .all 3 (.imp (.member 0 3) (.ex 2
  (namedBoth (.member 1 2) (namedBoth (graphFormula 6 2 3)
    (.all 4 (.imp (namedBoth (.member 1 4) (graphFormula 6 4 3)) (.equal 4 2)))))))

private def secondBackClause : Formula := .all 3 (.imp (.member 8 3) (.ex 2
  (namedBoth (.member 1 2) (namedBoth (graphFormula 7 2 3)
    (.all 4 (.imp (namedBoth (.member 1 4) (graphFormula 7 4 3)) (.equal 4 2)))))))

theorem first_bijection_alignment : firstBijection = namedBoth firstClause firstBackClause := by decide

theorem second_bijection_alignment : secondBijection = namedBoth secondClause secondBackClause := by decide

/-- Both actual matrices imply the forward clauses and so provide a span
graph over the entire common candidate source. The output is only the
endpoint-guarded span relation, not yet its bijection/order proof. -/
def span_from_input_matrices : KDerivation
    (imp firstMatrix.encode (imp secondMatrix.encode (imp (namedCandidate 1).encode
      (existsCode 9 (replace 10 1 spanComposition).encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(namedCandidate 1).encode,secondMatrix.encode,firstMatrix.encode]
  have hd : Context Γ (namedCandidate 1).encode := .head _ _
  have hs : Context Γ secondMatrix.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ firstMatrix.encode := .hypothesis (by simp [Γ])
  have hb1 : Context Γ firstBijection.encode := Context.conjunctionLeft hf
  have hb2 : Context Γ secondBijection.encode := Context.conjunctionLeft hs
  rw [first_bijection_alignment] at hb1
  rw [second_bijection_alignment] at hb2
  have hc1 : Context Γ firstClause.encode := Context.conjunctionLeft hb1
  have hc2 : Context Γ secondClause.encode := Context.conjunctionLeft hb2
  exact .mp hd (.mp hc2 (.mp hc1 (.closed common_source_span)))

theorem span_from_input_matrices_certificate :
    theoremCode (certificate span_from_input_matrices) =
      imp firstMatrix.encode (imp secondMatrix.encode (imp (namedCandidate 1).encode
        (existsCode 9 (replace 10 1 spanComposition).encode))) :=
  certificate_correct span_from_input_matrices

end PASoundness.PAtoCompactCommonSourceSpanInputMatrices

#print axioms PASoundness.PAtoCompactCommonSourceSpanInputMatrices.firstBijection
#print axioms PASoundness.PAtoCompactCommonSourceSpanInputMatrices.firstOrder
#print axioms PASoundness.PAtoCompactCommonSourceSpanInputMatrices.firstMatrix
#print axioms PASoundness.PAtoCompactCommonSourceSpanInputMatrices.secondBijection
#print axioms PASoundness.PAtoCompactCommonSourceSpanInputMatrices.secondOrder
#print axioms PASoundness.PAtoCompactCommonSourceSpanInputMatrices.secondMatrix
#print axioms PASoundness.PAtoCompactCommonSourceSpanInputMatrices.first_bijection_alignment
#print axioms PASoundness.PAtoCompactCommonSourceSpanInputMatrices.second_bijection_alignment
#print axioms PASoundness.PAtoCompactCommonSourceSpanInputMatrices.span_from_input_matrices
#print axioms PASoundness.PAtoCompactCommonSourceSpanInputMatrices.span_from_input_matrices_certificate
