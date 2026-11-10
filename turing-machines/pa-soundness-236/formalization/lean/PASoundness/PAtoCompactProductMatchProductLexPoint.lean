import PASoundness.PAtoCompactProductCleanLexTransfer
import PASoundness.PAtoCompactProductMatchTargetOutput
import PASoundness.PAtoCompactScopedActiveReplace

/-! The actual product lexicographic clauses, specialized at two source or
target triples. Their endpoint-membership and triple-edge guards remain part
of the displayed point formulas. This does not establish match-graph order. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchProductLexPoint

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductCleanLexTransfer
open PASoundness.PAtoCompactProductMatchTargetOutput PASoundness.PAtoCompactScopedActiveReplace

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourcePoint : Formula := replace 9 52 (replace 8 51 (replace 7 50
  (replace 5 32 (replace 4 31 (replace 3 30 (point 6))))))

/-- The source product matrix implies its exact guarded lex comparison at
coordinates 30,31,32 and 50,51,52. -/
def source_point : KDerivation (imp productMatrix.encode sourcePoint.encode) := by
  let f₃ : Formula := .all 4 (.all 5 (.all 7 (.all 8 (.all 9 (point 6)))))
  let f₄ : Formula := replace 3 30 (.all 5 (.all 7 (.all 8 (.all 9 (point 6)))))
  let f₅ : Formula := replace 4 31 (replace 3 30 (.all 7 (.all 8 (.all 9 (point 6)))))
  let f₇ : Formula := replace 5 32 (replace 4 31 (replace 3 30 (.all 8 (.all 9 (point 6)))))
  let f₈ : Formula := replace 7 50 (replace 5 32 (replace 4 31 (replace 3 30 (.all 9 (point 6)))))
  let f₉ : Formula := replace 8 51 (replace 7 50 (replace 5 32
    (replace 4 31 (replace 3 30 (point 6)))))
  have h₃ := universalInstance 3 30 f₃ (by decide) (by decide) (by decide)
  have hs₃ : replace 3 30 f₃ = .all 4 f₄ := by decide
  rw [hs₃] at h₃
  have h₄ := universalInstance 4 31 f₄ (by decide) (by decide) (by decide)
  have hs₄ : replace 4 31 f₄ = .all 5 f₅ := by decide
  rw [hs₄] at h₄
  have h₅ := universalInstance 5 32 f₅ (by decide) (by decide) (by decide)
  have hs₅ : replace 5 32 f₅ = .all 7 f₇ := by decide
  rw [hs₅] at h₅
  have h₇ := universalInstance 7 50 f₇ (by decide) (by decide) (by decide)
  have hs₇ : replace 7 50 f₇ = .all 8 f₈ := by decide
  rw [hs₇] at h₇
  have h₈ := universalInstance 8 51 f₈ (by decide) (by decide) (by decide)
  have hs₈ : replace 8 51 f₈ = .all 9 f₉ := by decide
  rw [hs₈] at h₈
  have h₉ := universalInstance 9 52 f₉ (by decide) (by decide) (by decide)
  have hs₉ : replace 9 52 f₉ = sourcePoint := by decide
  rw [hs₉] at h₉
  have hlex : KDerivation (imp lexFormula.encode sourcePoint.encode) := by
    rw [original_shape]
    simpa [f₃, Formula.encode] using compose h₃ (compose h₄ (compose h₅ (compose h₇ (compose h₈ h₉))))
  apply Context.closeEmpty
  apply Context.deduction
  have hm : Context [productMatrix.encode] productMatrix.encode := .head _ _
  change Context [productMatrix.encode] (both forwardFormula.encode
    (both reverseFormula.encode lexFormula.encode)) at hm
  exact .mp (Context.conjunctionRight (Context.conjunctionRight hm)) (.closed hlex)

def sourceFrame : Formula := .imp productMatrix sourcePoint
def targetPoint : Formula := replace 52 55 (replace 51 54 (replace 50 53
  (replace 32 35 (replace 31 34 (replace 30 33 (replace 0 42 (replace 1 43
    (replace 2 44 (replace 6 45 sourcePoint)))))))))
def targetFrame : Formula := .imp targetMatrix targetPoint

theorem target_frame_shape : replace 52 55 (replace 51 54 (replace 50 53
    (replace 32 35 (replace 31 34 (replace 30 33 (replace 0 42 (replace 1 43
      (replace 2 44 (replace 6 45 sourceFrame))))))))) = targetFrame := by decide

/-- The target product matrix implies the corresponding guarded comparison at
coordinates 33,34,35 and 53,54,55. -/
def target_point : KDerivation (imp targetMatrix.encode targetPoint.encode) := by
  have h0 : KDerivation sourceFrame.encode := by simpa [sourceFrame, Formula.encode] using source_point
  have h1 := replace_derivation 6 45 sourceFrame (by decide) (by decide) h0
  have h2 := replace_derivation 2 44 (replace 6 45 sourceFrame) (by decide) (by decide) h1
  have h3 := replace_derivation 1 43 (replace 2 44 (replace 6 45 sourceFrame)) (by decide) (by decide) h2
  have h4 := replace_derivation 0 42 (replace 1 43 (replace 2 44 (replace 6 45 sourceFrame))) (by decide) (by decide) h3
  have h5 := replace_derivation 30 33 (replace 0 42 (replace 1 43 (replace 2 44 (replace 6 45 sourceFrame)))) (by decide) (by decide) h4
  have h6 := replace_derivation 31 34 (replace 30 33 (replace 0 42 (replace 1 43 (replace 2 44 (replace 6 45 sourceFrame))))) (by decide) (by decide) h5
  have h7 := replace_derivation 32 35 (replace 31 34 (replace 30 33 (replace 0 42 (replace 1 43 (replace 2 44 (replace 6 45 sourceFrame)))))) (by decide) (by decide) h6
  have h8 := replace_derivation 50 53 (replace 32 35 (replace 31 34 (replace 30 33 (replace 0 42 (replace 1 43 (replace 2 44 (replace 6 45 sourceFrame))))))) (by decide) (by decide) h7
  have h9 := replace_derivation 51 54 (replace 50 53 (replace 32 35 (replace 31 34 (replace 30 33 (replace 0 42 (replace 1 43 (replace 2 44 (replace 6 45 sourceFrame)))))))) (by decide) (by decide) h8
  have h10 := replace_derivation 52 55 (replace 51 54 (replace 50 53 (replace 32 35 (replace 31 34 (replace 30 33 (replace 0 42 (replace 1 43 (replace 2 44 (replace 6 45 sourceFrame))))))))) (by decide) (by decide) h9
  rw [target_frame_shape] at h10
  simpa [targetFrame, Formula.encode] using h10

theorem source_point_certificate : theoremCode (certificate source_point) =
    imp productMatrix.encode sourcePoint.encode := certificate_correct _
theorem target_point_certificate : theoremCode (certificate target_point) =
    imp targetMatrix.encode targetPoint.encode := certificate_correct _

end PASoundness.PAtoCompactProductMatchProductLexPoint

#print axioms PASoundness.PAtoCompactProductMatchProductLexPoint.source_point
#print axioms PASoundness.PAtoCompactProductMatchProductLexPoint.target_point
#print axioms PASoundness.PAtoCompactProductMatchProductLexPoint.source_point_certificate
#print axioms PASoundness.PAtoCompactProductMatchProductLexPoint.target_point_certificate
