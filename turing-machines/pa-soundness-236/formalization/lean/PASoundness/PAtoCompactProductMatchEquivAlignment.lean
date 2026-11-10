import PASoundness.PAtoCompactProductMatchClauseAlpha
import PASoundness.PAtoCompactAlphaCongruence
import PASoundness.PAtoCompactCancellationEquivAlpha100
import PASoundness.PAtoCompactScopedActiveReplace

/-! Capture-safe finite K alignment of the explicit one-graph product
isomorphism with the allocator-100 `equivAt` formula. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchEquivAlignment

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactAlphaCongruence
open PASoundness.PAtoCompactProductMatchExplicitIsomorphism PASoundness.PAtoCompactProductMatchClauseAlpha
open PASoundness.PAtoCompactCancellationGuardInputs PASoundness.PAtoCompactCancellationEquivAlpha100
open PASoundness.PAtoCompactScopedActiveReplace

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def highBody : Formula := replace 44 42 (replace 2 40 isoBody)
def highExplicit : Formula := replace 44 42 (replace 2 40 explicitIsomorphism)
def baseMatrix : Formula := replace 1 42 (replace 0 40 (namedBoth bijectionFormula orderFormula))
def canonicalMatrix : Formula := replace 6 58 baseMatrix

theorem high_body_shape : highBody = namedBoth (namedBoth highForward highReverse) highOrder := by decide
theorem matrix_shape : canonicalMatrix = namedBoth (namedBoth canonicalForward canonicalReverse) canonicalOrder := by decide
theorem high_explicit_shape : highExplicit = .ex 58 highBody := by decide
theorem input_equivalent_shape : inputEquivalent = .ex 6 baseMatrix := by decide

def high_body_to_matrix : KDerivation (imp highBody.encode canonicalMatrix.encode) := by
  have h := andF_congr (andF_congr forwardAlpha reverseAlpha) orderAlpha
  change ProofEquiv (namedBoth (namedBoth highForward highReverse) highOrder)
    (namedBoth (namedBoth canonicalForward canonicalReverse) canonicalOrder) at h
  simpa [high_body_shape, matrix_shape] using h.forward

def high_explicit_to_allocated : KDerivation
    (imp highExplicit.encode (equivAt 100 40 42).encode) := by
  have hmap := existsCongr 58 high_body_to_matrix
  have halpha := (existentialAlpha 6 58 baseMatrix (by decide) (by decide) (by decide)).2
  change KDerivation (imp (existsCode 58 canonicalMatrix.encode) (existsCode 6 baseMatrix.encode)) at halpha
  have hin : KDerivation (imp (existsCode 6 baseMatrix.encode) (equivAt 100 40 42).encode) := by
    simpa [input_equivalent_shape, Formula.encode] using input_alpha.1
  have h := compose hmap (compose halpha hin)
  simpa [high_explicit_shape, input_equivalent_shape, Formula.encode] using h

def alignmentFrame : Formula := .imp highExplicit (equivAt 100 40 42)
theorem alignment_frame_shape : replace 42 44 (replace 40 2 alignmentFrame) =
    .imp explicitIsomorphism (equivAt 100 2 44) := by decide

/-- The exact explicit isomorphism implies the standard allocator-100
quotient-equivalence instance; the two represented operands may coincide. -/
def explicit_to_equivAt : KDerivation
    (imp explicitIsomorphism.encode (equivAt 100 2 44).encode) := by
  have h0 : KDerivation alignmentFrame.encode := by
    simpa [alignmentFrame, Formula.encode] using high_explicit_to_allocated
  have h1 := replace_derivation 40 2 alignmentFrame (by decide) (by decide) h0
  have h2 := replace_derivation 42 44 (replace 40 2 alignmentFrame) (by decide) (by decide) h1
  rw [alignment_frame_shape] at h2
  simpa [Formula.encode] using h2

theorem explicit_to_equivAt_certificate : theoremCode (certificate explicit_to_equivAt) =
    imp explicitIsomorphism.encode (equivAt 100 2 44).encode := certificate_correct _

end PASoundness.PAtoCompactProductMatchEquivAlignment

#print axioms PASoundness.PAtoCompactProductMatchEquivAlignment.high_body_to_matrix
#print axioms PASoundness.PAtoCompactProductMatchEquivAlignment.high_explicit_to_allocated
#print axioms PASoundness.PAtoCompactProductMatchEquivAlignment.explicit_to_equivAt
#print axioms PASoundness.PAtoCompactProductMatchEquivAlignment.explicit_to_equivAt_certificate
