import PASoundness.PAtoCompactMultiplicationZeroAllocated
import PASoundness.PAtoCompactZeroBaseTransport
import PASoundness.PAtoCompactDomainClassification

/-! A finite K zero-left-factor base for the proposed first-coordinate
multiplication induction. The actual successor schema and full product
totality remain separate obligations. The test and allocation names below
are syntactic labels; no distinctness of represented objects is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationInductionZeroBase
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactZeroBaseTransport PASoundness.PAtoCompactDomainClassification
open PASoundness.PAtoCompactMultiplicationZeroAllocated
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The selected zero test implies existence of a candidate output for the
actual allocated multiplication relation, for an arbitrary second factor. -/
def zero_left_fixed : KDerivation
    (imp (zeroCode 205 207)
      (existsCode 32 (andF (domainAt 300 32) (mulAt 300 205 30 32)).encode)) := by
  have hz : KDerivation (imp (zeroCode 205 207) (zeroAt 300 205).encode) := by
    have h := zero_test_rename 205 207 303 (by decide) (by decide) (by decide)
    simpa [zeroAt_shape, zeroCode, Formula.encode, Formula.not, CompactProof.neg] using h
  exact compose hz (zero_product_exists 300 205 30 32
    (by decide) (by decide) (by decide) (by decide) (by decide))

theorem zero_left_fixed_certificate : theoremCode (certificate zero_left_fixed) =
    imp (zeroCode 205 207)
      (existsCode 32 (andF (domainAt 300 32) (mulAt 300 205 30 32)).encode) :=
  certificate_correct zero_left_fixed
end PASoundness.PAtoCompactMultiplicationInductionZeroBase
#print axioms PASoundness.PAtoCompactMultiplicationInductionZeroBase.zero_left_fixed
#print axioms PASoundness.PAtoCompactMultiplicationInductionZeroBase.zero_left_fixed_certificate
