import PASoundness.PAtoCompactMultiplicationCanonicalBaseStep
import PASoundness.PAtoCompactAdjunction

/-! The literal product matrix at graph name 64 introduces the canonical
existential product relation for the same graph value. The matrix is an
explicit K antecedent; no graph collection, multiplication totality, or PA
proof transport is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatrixGraph64Intro
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactMultiplicationCanonicalBaseStep
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Matrix body of the canonical product formula with its inputs changed to
38,31,45, before choosing its existential graph. -/
def canonicalBody : Formula := replace 2 45 (replace 1 31 (replace 0 38 productMatrix))

/-- The same matrix with the displayed graph value named 64. -/
def matrix64 : Formula := replace 6 64 canonicalBody

/-- Input renaming retains the graph binder of the raw new-product formula. -/
theorem raw_new_shape : rawNew = .ex 6 canonicalBody := by decide

/-- A single graph64 satisfying the matrix witnesses the actual raw new
product; this is literal K existential introduction, without graph existence
or semantic soundness assumptions. -/
def matrix_to_raw : KDerivation (imp matrix64.encode rawNew.encode) := by
  have h := exists_variable_intro 6 64 canonicalBody (by decide) (by decide) (by decide)
  simpa only [matrix64, raw_new_shape, Formula.encode] using h

theorem matrix_to_raw_certificate : theoremCode (certificate matrix_to_raw) =
    imp matrix64.encode rawNew.encode := certificate_correct matrix_to_raw
end PASoundness.PAtoCompactProductMatrixGraph64Intro
#print axioms PASoundness.PAtoCompactProductMatrixGraph64Intro.raw_new_shape
#print axioms PASoundness.PAtoCompactProductMatrixGraph64Intro.matrix_to_raw
#print axioms PASoundness.PAtoCompactProductMatrixGraph64Intro.matrix_to_raw_certificate
