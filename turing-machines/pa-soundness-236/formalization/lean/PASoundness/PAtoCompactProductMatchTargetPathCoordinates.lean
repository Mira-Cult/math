import PASoundness.PAtoCompactProductMatchTargetCoordinatesFromMatrix
import PASoundness.PAtoCompactScopedActiveReplace

/-! Align target-coordinate uniqueness with the two matching-path labels.
No graph reverse-uniqueness conclusion is asserted here. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchTargetPathCoordinates

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactProductMatchTargetOutput
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactProductMatchTargetCoordinateUnique
open PASoundness.PAtoCompactProductMatchTargetTwoCoordinates PASoundness.PAtoCompactProductMatchTargetCoordinatesFromMatrix

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def matrixFrame : Formula := .imp targetMatrix (.imp (.member 44 55)
  (.imp coordinateGuard coordinateEquality))
def pathGuard : Formula := namedBoth
  (namedBoth (.member 42 33) (namedBoth (.member 43 34) (targetTriple 33 34 55)))
  (namedBoth (.member 42 53) (namedBoth (.member 43 54) (targetTriple 53 54 55)))
def pathEquality : Formula := namedBoth (.equal 33 53) (.equal 34 54)
def pathFrame : Formula := .imp targetMatrix (.imp (.member 44 55) (.imp pathGuard pathEquality))

theorem path_frame_shape : replace 61 54 (replace 60 53 (replace 54 34 (replace 53 33 matrixFrame))) = pathFrame := by decide

def target_path_coordinates_unique : KDerivation
    (imp targetMatrix.encode (imp (member 44 55) (imp pathGuard.encode pathEquality.encode))) := by
  have h0 : KDerivation matrixFrame.encode := by
    simpa [matrixFrame, Formula.encode] using target_coordinates_from_matrix
  have h1 := replace_derivation 53 33 matrixFrame (by decide) (by decide) h0
  have h2 := replace_derivation 54 34 (replace 53 33 matrixFrame) (by decide) (by decide) h1
  have h3 := replace_derivation 60 53 (replace 54 34 (replace 53 33 matrixFrame)) (by decide) (by decide) h2
  have h4 := replace_derivation 61 54 (replace 60 53 (replace 54 34 (replace 53 33 matrixFrame)))
    (by decide) (by decide) h3
  rw [path_frame_shape] at h4
  simpa [pathFrame, Formula.encode] using h4

theorem target_path_coordinates_unique_certificate : theoremCode (certificate target_path_coordinates_unique) =
    imp targetMatrix.encode (imp (member 44 55) (imp pathGuard.encode pathEquality.encode)) := certificate_correct _

end PASoundness.PAtoCompactProductMatchTargetPathCoordinates

#print axioms PASoundness.PAtoCompactProductMatchTargetPathCoordinates.target_path_coordinates_unique
#print axioms PASoundness.PAtoCompactProductMatchTargetPathCoordinates.target_path_coordinates_unique_certificate
