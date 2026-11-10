import PASoundness.PAtoCompactProductOutputReversePoint
import PASoundness.PAtoCompactProductOutputActualPoint
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactSuccGraphOutputLift

/-! Pointwise reverse coverage of the supplied actual output graph. A target
member is traced to one source output and source-product coordinate pair;
the same pair witnesses a target-graph triple. No uniqueness is asserted. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputReverseCoverage

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductOutputImagePoint
open PASoundness.PAtoCompactProductOutputPreimagePoint PASoundness.PAtoCompactProductOutputReverseReconstruct
open PASoundness.PAtoCompactProductOutputReversePoint PASoundness.PAtoCompactProductOutputActualPoint
open PASoundness.PAtoCompactProductOutputCollectionInsideConditional PASoundness.PAtoCompactProductOutputForwardFromReverse

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceFrame : Formula := .imp sourceMatrix (.imp firstBijection (.imp (.member 42 33)
  (.ex 32 (.ex 30 (.ex 31 reconstructed)))))
def relocatedMatrix : Formula := replace 81 44 (replace 80 43 sourceMatrix)
def relocatedBody : Formula := replace 81 44 (replace 80 43 reconstructed)
def relocatedReverse : Formula := replace 81 44 (replace 80 43 reverseBody)
def relocatedTail : Formula := replace 81 44 (replace 80 43
  (namedBoth PAtoCompactProductOutputForwardFromReverse.selectedTriple PAtoCompactProductOutputForwardFromReverse.reverseTail))
def reverseResult : Formula := namedBoth (.member 43 30)
  (namedBoth (.member 44 31) PAtoCompactProductOutputActualPoint.selectedTriple)

theorem relocated_frame_shape : replace 81 44 (replace 80 43 sourceFrame) = .imp relocatedMatrix
    (.imp firstBijection (.imp (.member 42 33) (.ex 32 (.ex 30 (.ex 31 relocatedBody))))) := by decide
theorem relocated_body_shape : relocatedBody = namedBoth preimage32
    (namedBoth relocatedReverse PAtoCompactProductOutputImagePoint.pairedBody) := by decide
theorem relocated_reverse_shape : relocatedReverse = namedBoth (.member 43 30)
    (namedBoth (.member 44 31) relocatedTail) := by decide

def relocated_reverse_exists : KDerivation (imp relocatedMatrix.encode (imp firstBijection.encode
    (imp (member 42 33) (existsCode 32 (existsCode 30 (existsCode 31 relocatedBody.encode)))))) := by
  have h0 : KDerivation sourceFrame.encode := by
    simpa [sourceFrame, CompactNamed.Formula.encode] using reverse_point_exists
  have h1 := replace_derivation 80 43 sourceFrame (by decide) (by decide) h0
  have h2 := replace_derivation 81 44 (replace 80 43 sourceFrame) (by decide) (by decide) h1
  simpa [relocated_frame_shape, CompactNamed.Formula.encode] using h2

def reverse_body_in_graph : KDerivation (imp actualInvariant.encode
    (imp relocatedBody.encode reverseResult.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [relocatedBody.encode,actualInvariant.encode]
  have hp : Context Γ relocatedBody.encode := .head _ _
  have hi : Context Γ actualInvariant.encode := .hypothesis (by simp [Γ])
  have hp' : Context Γ (both preimage32.encode
      (both relocatedReverse.encode PAtoCompactProductOutputImagePoint.pairedBody.encode)) := by
    simpa [relocated_body_shape, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using hp
  have hr : Context Γ (both (member 43 30) (both (member 44 31) relocatedTail.encode)) := by
    simpa [relocated_reverse_shape, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using Context.conjunctionLeft (Context.conjunctionRight hp')
  have hx := Context.conjunctionLeft hr
  have hy := Context.conjunctionLeft (Context.conjunctionRight hr)
  have hf := Context.conjunctionRight (Context.conjunctionRight hp')
  have hout := Context.mp hf (Context.mp hy (Context.mp hx (Context.mp hi (.closed selected_body_in_graph))))
  simpa [reverseResult, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
    Context.conjunctionIntro hx (Context.conjunctionIntro hy (Context.conjunctionRight hout))

/-- Every target member has source-factor coordinates with an actual triple
in this same graph58. Uniqueness of the coordinates remains separate. -/
def reverse_coverage : KDerivation (imp assumptions.encode (imp actualInvariant.encode
    (imp (member 42 33) (existsCode 30 (existsCode 31 reverseResult.encode))))) := by
  have h31 := conditionalExistsCongr 31 (free_vacuity 31 actualInvariant (by decide)) reverse_body_in_graph
  have h30 := conditionalExistsCongr 30 (free_vacuity 30 actualInvariant (by decide)) h31
  have h32 := guarded_exists_left 32 actualInvariant.encode (existsCode 30 (existsCode 31 relocatedBody.encode))
    (existsCode 30 (existsCode 31 reverseResult.encode))
    (free_vacuity 32 actualInvariant (by decide))
    ((Formula.ex 30 (.ex 31 reverseResult)).vacuity 32 (by decide)) h30
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 42 33,actualInvariant.encode,assumptions.encode]
  have hy : Context Γ (member 42 33) := .head _ _
  have hi : Context Γ actualInvariant.encode := .hypothesis (by simp [Γ])
  have ha : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
  have ha' : Context Γ (both relocatedMatrix.encode firstBijection.encode) := by
    simpa [assumptions, relocatedMatrix, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using ha
  have he := Context.mp hy (Context.mp (Context.conjunctionRight ha')
    (Context.mp (Context.conjunctionLeft ha') (.closed relocated_reverse_exists)))
  exact .mp he (.mp hi (.closed h32))

theorem reverse_coverage_certificate : theoremCode (certificate reverse_coverage) =
    imp assumptions.encode (imp actualInvariant.encode (imp (member 42 33)
      (existsCode 30 (existsCode 31 reverseResult.encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputReverseCoverage

#print axioms PASoundness.PAtoCompactProductOutputReverseCoverage.relocated_reverse_exists
#print axioms PASoundness.PAtoCompactProductOutputReverseCoverage.reverse_body_in_graph
#print axioms PASoundness.PAtoCompactProductOutputReverseCoverage.reverse_coverage
#print axioms PASoundness.PAtoCompactProductOutputReverseCoverage.reverse_coverage_certificate
