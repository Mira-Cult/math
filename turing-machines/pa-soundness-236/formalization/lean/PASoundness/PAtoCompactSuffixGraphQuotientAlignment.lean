import PASoundness.PAtoCompactRestrictedEquivalentTarget
import PASoundness.PAtoCompactScopedActiveReplace

/-! Instantiation of the already proved preparation equivalence at suffix
 endpoints. This is a K proof transformation; it does not construct a suffix
 graph or discharge any coverage or order clause. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuffixGraphQuotientAlignment
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactRestrictedEquivalentTarget
open PASoundness.PAtoCompactScopedActiveReplace
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The original quotient-equivalence syntax, with source and target free
names safely replaced by 40 and 41. -/
def suffixEquivalent : Formula := replace 1 41 (replace 0 40 equivalentFormula)

/-- The corresponding prepared graph8 formula, with the same endpoints. -/
def suffixPrepared : Formula := replace 1 41 (replace 0 40 preparedEquivalent)

private def frame : Formula := .imp preparedEquivalent equivalentFormula
private def firstFrame : Formula := replace 0 40 frame

/-- Once the same restricted-graph matrix has been assembled in the literal
prepared syntax, it entails the canonical named isomorphism at suffix names
40 and 41. This is finite K proof data; its endpoints may denote equal objects. -/
noncomputable def suffix_prepared_to_equivalent : KDerivation
    (imp suffixPrepared.encode suffixEquivalent.encode) := by
  have hbase : KDerivation frame.encode := by
    simpa only [frame,Formula.encode] using prepare_equivalent.backward
  have h40 := replace_derivation 0 40 frame (by decide) (by decide) hbase
  have h41 := replace_derivation 1 41 firstFrame (by decide) (by decide)
    (by simpa only [firstFrame] using h40)
  simpa only [firstFrame,frame,suffixPrepared,suffixEquivalent,replace,Formula.encode] using h41

theorem suffix_prepared_to_equivalent_certificate :
    theoremCode (certificate suffix_prepared_to_equivalent) =
      imp suffixPrepared.encode suffixEquivalent.encode :=
  certificate_correct suffix_prepared_to_equivalent

end PASoundness.PAtoCompactSuffixGraphQuotientAlignment

#print axioms PASoundness.PAtoCompactSuffixGraphQuotientAlignment.suffixEquivalent
#print axioms PASoundness.PAtoCompactSuffixGraphQuotientAlignment.suffixPrepared
#print axioms PASoundness.PAtoCompactSuffixGraphQuotientAlignment.suffix_prepared_to_equivalent
#print axioms PASoundness.PAtoCompactSuffixGraphQuotientAlignment.suffix_prepared_to_equivalent_certificate
