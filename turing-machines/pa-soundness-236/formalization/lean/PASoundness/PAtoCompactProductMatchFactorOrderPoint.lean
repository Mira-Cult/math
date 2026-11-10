import PASoundness.PAtoCompactOrderIsoInstance
import PASoundness.PAtoCompactScopedActiveReplace

/-! Literal pointwise order instances for the two factor-isomorphism
graphs in a product match. Each order clause and its endpoint/edge guards
remain explicit. This does not prove order of the collected match graph. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchFactorOrderPoint

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoInstance
open PASoundness.PAtoCompactScopedActiveReplace

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def point : Formula := replace 5 53 (replace 3 33 (replace 4 50 (replace 2 30 orderMatrix)))
def firstOrder : Formula := replace 1 42 (replace 6 40 orderFormula)
def firstPoint : Formula := replace 1 42 (replace 6 40 point)
def firstFrame : Formula := .imp firstOrder firstPoint

/-- Capture-safe specialization of the actual four-quantifier order clause. -/
private def fixed_point : KDerivation (imp orderFormula.encode point.encode) := by
  let f₂ : Formula := .all 4 (.all 3 (.all 5 orderMatrix))
  let f₄ : Formula := replace 2 30 (.all 3 (.all 5 orderMatrix))
  let f₃ : Formula := replace 4 50 (replace 2 30 (.all 5 orderMatrix))
  let f₅ : Formula := replace 3 33 (replace 4 50 (replace 2 30 orderMatrix))
  have h₂ := universalInstance 2 30 f₂ (by decide) (by decide) (by decide)
  have h₂s : replace 2 30 f₂ = .all 4 f₄ := by decide
  rw [h₂s] at h₂
  have h₄ := universalInstance 4 50 f₄ (by decide) (by decide) (by decide)
  have h₄s : replace 4 50 f₄ = .all 3 f₃ := by decide
  rw [h₄s] at h₄
  have h₃ := universalInstance 3 33 f₃ (by decide) (by decide) (by decide)
  have h₃s : replace 3 33 f₃ = .all 5 f₅ := by decide
  rw [h₃s] at h₃
  have h₅ := universalInstance 5 53 f₅ (by decide) (by decide) (by decide)
  have h₅s : replace 5 53 f₅ = point := by decide
  rw [h₅s] at h₅
  have hshape : orderFormula = .all 2 f₂ := by decide
  rw [hshape]
  simpa [Formula.encode] using compose h₂ (compose h₄ (compose h₃ h₅))

theorem first_frame_shape : replace 1 42 (replace 6 40 (.imp orderFormula point)) = firstFrame := by decide

/-- The first supplied factor-order clause implies its guarded comparison at
source 30,50 and target 33,53. -/
def first_order_point : KDerivation (imp firstOrder.encode firstPoint.encode) := by
  let f : Formula := .imp orderFormula point
  have h0 : KDerivation f.encode := by simpa [f, Formula.encode] using fixed_point
  have h1 := replace_derivation 6 40 f (by decide) (by decide) h0
  have h2 := replace_derivation 1 42 (replace 6 40 f) (by decide) (by decide) h1
  change KDerivation (replace 1 42 (replace 6 40 (.imp orderFormula point))).encode at h2
  rw [first_frame_shape] at h2
  simpa [firstFrame, Formula.encode] using h2

def secondOrder : Formula := replace 0 1 (replace 42 43 (replace 40 41 firstOrder))
def secondPoint : Formula := replace 53 54 (replace 33 34 (replace 50 51
  (replace 30 31 (replace 0 1 (replace 42 43 (replace 40 41 firstPoint))))))
def secondFrame : Formula := .imp secondOrder secondPoint

theorem second_frame_shape : replace 53 54 (replace 33 34 (replace 50 51 (replace 30 31
    (replace 0 1 (replace 42 43 (replace 40 41 firstFrame)))))) = secondFrame := by decide

/-- The second supplied factor-order clause implies its guarded comparison at
source 31,51 and target 34,54. -/
def second_order_point : KDerivation (imp secondOrder.encode secondPoint.encode) := by
  have h0 : KDerivation firstFrame.encode := by simpa [firstFrame, Formula.encode] using first_order_point
  have h1 := replace_derivation 40 41 firstFrame (by decide) (by decide) h0
  have h2 := replace_derivation 42 43 (replace 40 41 firstFrame) (by decide) (by decide) h1
  have h3 := replace_derivation 0 1 (replace 42 43 (replace 40 41 firstFrame)) (by decide) (by decide) h2
  have h4 := replace_derivation 30 31 (replace 0 1 (replace 42 43 (replace 40 41 firstFrame)))
    (by decide) (by decide) h3
  have h5 := replace_derivation 50 51 (replace 30 31 (replace 0 1 (replace 42 43 (replace 40 41 firstFrame))))
    (by decide) (by decide) h4
  have h6 := replace_derivation 33 34 (replace 50 51 (replace 30 31
    (replace 0 1 (replace 42 43 (replace 40 41 firstFrame))))) (by decide) (by decide) h5
  have h7 := replace_derivation 53 54 (replace 33 34 (replace 50 51 (replace 30 31
    (replace 0 1 (replace 42 43 (replace 40 41 firstFrame)))))) (by decide) (by decide) h6
  rw [second_frame_shape] at h7
  simpa [secondFrame, Formula.encode] using h7

theorem first_order_point_certificate : theoremCode (certificate first_order_point) =
    imp firstOrder.encode firstPoint.encode := certificate_correct _
theorem second_order_point_certificate : theoremCode (certificate second_order_point) =
    imp secondOrder.encode secondPoint.encode := certificate_correct _

end PASoundness.PAtoCompactProductMatchFactorOrderPoint

#print axioms PASoundness.PAtoCompactProductMatchFactorOrderPoint.first_order_point
#print axioms PASoundness.PAtoCompactProductMatchFactorOrderPoint.second_order_point
#print axioms PASoundness.PAtoCompactProductMatchFactorOrderPoint.first_order_point_certificate
#print axioms PASoundness.PAtoCompactProductMatchFactorOrderPoint.second_order_point_certificate
