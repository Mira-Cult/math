import PASoundness.PAtoCompactOrdinalAddition
import PASoundness.PAtoCompactFilterInstantiation

/-! Capture-safe test-binder alpha conversion for the two concrete suffix
filters used in rebasing the proper-cut graph. This supplies only the filter
conversions; it constructs no graph or isomorphism. -/
namespace PASoundness.PAtoCompactSuffixRebaseFilterAlpha
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactFilterInstantiation
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def sourceBody : Formula := namedFilterBody 32 34 35 (Formula.member 33 35).not
private def targetBody : Formula := namedFilterBody 8 38 35 (Formula.member 41 35).not

/-- The source filter with its test binder moved away from 35. -/
def sourceFilter42 : Formula := .all 42 (namedFilterBody 32 34 42 (Formula.member 33 42).not)
/-- The target suffix in the literal source-addition syntax, with its three
free endpoint names relabelled while retaining test binder 35. -/
def targetSuffix : Formula := replace 34 38 (replace 33 41 (replace 32 8 suffixFormula))
/-- The target filter with its test binder moved away from 35. -/
def targetFilter43 : Formula := .all 43 (namedFilterBody 8 38 43 (Formula.member 41 43).not)

private theorem source_shape : suffixFormula = .all 35 sourceBody := by rfl
private theorem target_shape : targetSuffix = .all 35 targetBody := by decide
private theorem source_replace : replace 35 42 sourceBody =
    namedFilterBody 32 34 42 (Formula.member 33 42).not := by decide
private theorem target_replace : replace 35 43 targetBody =
    namedFilterBody 8 38 43 (Formula.member 41 43).not := by decide

/-- The original source suffix yields the same filter with test name 42. -/
def source_suffix_to_filter42 : KDerivation (imp suffixFormula.encode sourceFilter42.encode) := by
  have h := (universalAlpha 35 42 sourceBody (by decide) (by decide) (by decide)).1
  rw [source_replace] at h
  rw [source_shape]
  simpa only [sourceFilter42, Formula.encode] using h

/-- The target suffix yields the same filter with test name 43. -/
def target_suffix_to_filter43 : KDerivation (imp targetSuffix.encode targetFilter43.encode) := by
  have h := (universalAlpha 35 43 targetBody (by decide) (by decide) (by decide)).1
  rw [target_replace] at h
  rw [target_shape]
  simpa only [targetFilter43, Formula.encode] using h

theorem source_suffix_to_filter42_certificate :
    theoremCode (certificate source_suffix_to_filter42) = imp suffixFormula.encode sourceFilter42.encode :=
  certificate_correct _

theorem target_suffix_to_filter43_certificate :
    theoremCode (certificate target_suffix_to_filter43) = imp targetSuffix.encode targetFilter43.encode :=
  certificate_correct _

end PASoundness.PAtoCompactSuffixRebaseFilterAlpha

#print axioms PASoundness.PAtoCompactSuffixRebaseFilterAlpha.sourceFilter42
#print axioms PASoundness.PAtoCompactSuffixRebaseFilterAlpha.targetSuffix
#print axioms PASoundness.PAtoCompactSuffixRebaseFilterAlpha.targetFilter43
#print axioms PASoundness.PAtoCompactSuffixRebaseFilterAlpha.source_suffix_to_filter42
#print axioms PASoundness.PAtoCompactSuffixRebaseFilterAlpha.target_suffix_to_filter43
#print axioms PASoundness.PAtoCompactSuffixRebaseFilterAlpha.source_suffix_to_filter42_certificate
#print axioms PASoundness.PAtoCompactSuffixRebaseFilterAlpha.target_suffix_to_filter43_certificate
