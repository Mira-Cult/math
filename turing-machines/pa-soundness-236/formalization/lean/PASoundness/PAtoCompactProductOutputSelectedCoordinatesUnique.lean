import PASoundness.PAtoCompactProductOutputSelectedPath
import PASoundness.PAtoCompactProductOutputOutsidePath

/-! When a queried path and the selected point have the same source output,
the source-product reverse clause compares their factor coordinates. Endpoint
membership and the selected reverse witness remain explicit. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputSelectedCoordinatesUnique

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductOutputPartialBase PASoundness.PAtoCompactProductOutputOutsidePath
open PASoundness.PAtoCompactProductOutputInsideSelected PASoundness.PAtoCompactProductOutputSelectedPath

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def reverseUnique : Formula := .imp (namedBoth (.member 43 7)
  (namedBoth (.member 44 8) (tripleFormula 7 8 74)))
  (namedBoth (.equal 7 30) (.equal 8 31))
def selectedTail : Formula := namedBoth (.member 44 31)
  (namedBoth (tripleFormula 30 31 74) (.all 7 (.all 8 reverseUnique)))
def queryTail : Formula := replace 33 60 (replace 31 57 (replace 30 56
  (.all 9 PAtoCompactProductOutputImageUnique.sourceUnique)))

theorem selected_reverse_shape : selectedReverse = namedBoth (.member 43 30) selectedTail := by decide
theorem source_tail_shape : sourceTail = namedBoth (tripleFormula 56 57 32) queryTail := by decide

def same_source_coordinates : KDerivation (imp relocatedBody.encode (imp endpointGuard.encode
    (imp (equal 32 74) (imp payloadAt.encode (both (equal 56 30) (equal 57 31)))))) := by
  have h7 := universalInstance 7 56 (.all 8 reverseUnique) (by decide) (by decide) (by decide)
  have h7shape : replace 7 56 (.all 8 reverseUnique) = .all 8 (replace 7 56 reverseUnique) := by decide
  rw [h7shape] at h7
  have h8 := universalInstance 8 57 (replace 7 56 reverseUnique) (by decide) (by decide) (by decide)
  have h8shape : replace 8 57 (replace 7 56 reverseUnique) = .imp
      (namedBoth (.member 43 56) (namedBoth (.member 44 57) (tripleFormula 56 57 74)))
      (namedBoth (.equal 56 30) (.equal 57 31)) := by decide
  rw [h8shape] at h8
  have hmove := (equalityReplace 32 74 (tripleFormula 56 57 32) (by decide) (by decide)).1
  have hmoveShape : replace 32 74 (tripleFormula 56 57 32) = tripleFormula 56 57 74 := by decide
  rw [hmoveShape] at hmove
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [payloadAt.encode,equal 32 74,endpointGuard.encode,relocatedBody.encode]
  have hp : Context Γ payloadAt.encode := .head _ _
  have heq : Context Γ (equal 32 74) := .hypothesis (by simp [Γ])
  have hend : Context Γ endpointGuard.encode := .hypothesis (by simp [Γ])
  have hsel : Context Γ relocatedBody.encode := .hypothesis (by simp [Γ])
  have hp' : Context Γ (both sourceAt.encode imageAt.encode) := by
    simpa [payload_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hp
  have hsource : Context Γ (both (member 0 32) sourceTail.encode) := by
    simpa [source_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionLeft hp'
  have htail : Context Γ (both (tripleFormula 56 57 32).encode queryTail.encode) := by
    simpa [source_tail_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionRight hsource
  have htriple := Context.mp (Context.conjunctionLeft htail) (Context.mp heq (.closed hmove))
  have hend' : Context Γ (both (member 43 56) (both (member 44 57) (member 42 60))) := by
    simpa [endpointGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hend
  have hsel' : Context Γ (both selectedReverse.encode selectedPair.encode) := by
    simpa [selected_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hsel
  have hreverse : Context Γ (both (member 43 30) (both (member 44 31)
      (both (tripleFormula 30 31 74).encode (allCode 7 (allCode 8 reverseUnique.encode))))) := by
    simpa [selected_reverse_shape, selectedTail, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using Context.conjunctionLeft hsel'
  have hu := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hreverse))
  have hu' := Context.mp (Context.mp hu (.closed h7)) (.closed h8)
  have hcompetitor : Context Γ (namedBoth (.member 43 56)
      (namedBoth (.member 44 57) (tripleFormula 56 57 74))).encode := by
    simpa [namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro (Context.conjunctionLeft hend')
        (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight hend')) htriple)
  simpa [namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
    Context.mp hcompetitor hu'

theorem same_source_coordinates_certificate : theoremCode (certificate same_source_coordinates) =
    imp relocatedBody.encode (imp endpointGuard.encode (imp (equal 32 74)
      (imp payloadAt.encode (both (equal 56 30) (equal 57 31))))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputSelectedCoordinatesUnique

#print axioms PASoundness.PAtoCompactProductOutputSelectedCoordinatesUnique.same_source_coordinates
#print axioms PASoundness.PAtoCompactProductOutputSelectedCoordinatesUnique.same_source_coordinates_certificate
