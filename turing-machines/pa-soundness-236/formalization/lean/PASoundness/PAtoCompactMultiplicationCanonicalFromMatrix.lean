import PASoundness.PAtoCompactMultiplicationCanonicalFromRetained
import PASoundness.PAtoCompactMultiplicationRetainedRawElim
import PASoundness.PAtoCompactProductMatrixGraph64Intro

/-! Combine the audited existential steps from a supplied finite K proof of the
actual product matrix at the same graph 64. The matrix proof remains an
explicit input; this module alone does not establish the canonical extension,
multiplication totality, or a PA bridge. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationCanonicalFromMatrix
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactForwardContextWithLex
open PASoundness.PAtoCompactProductMatrixGraph64Intro
open PASoundness.PAtoCompactMultiplicationCanonicalBaseStep
open PASoundness.PAtoCompactMultiplicationCanonicalFromRetained
open PASoundness.PAtoCompactMultiplicationRetainedRawElim
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A supplied K proof of the exact product matrix from the retained shared
context implies the canonical first-factor multiplication successor step. -/
noncomputable def canonical_from_matrix
    (matrix : KDerivation (imp contextWithLex.encode matrix64.encode)) :
    KDerivation canonical100.encode :=
  canonical_from_retained (retained_to_rawNew (compose matrix matrix_to_raw))

theorem canonical_from_matrix_certificate
    (matrix : KDerivation (imp contextWithLex.encode matrix64.encode)) :
    theoremCode (certificate (canonical_from_matrix matrix)) = canonical100.encode :=
  certificate_correct _
end PASoundness.PAtoCompactMultiplicationCanonicalFromMatrix
#print axioms PASoundness.PAtoCompactMultiplicationCanonicalFromMatrix.canonical_from_matrix
#print axioms PASoundness.PAtoCompactMultiplicationCanonicalFromMatrix.canonical_from_matrix_certificate
