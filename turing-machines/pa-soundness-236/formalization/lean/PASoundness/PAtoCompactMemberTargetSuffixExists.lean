import PASoundness.PAtoCompactAdditionSuffixClosed
import PASoundness.PAtoCompactScopedActiveReplace
import PASoundness.PAtoCompactMemberCutRawTargetIntro

/-! The target result/cut suffix exists by K selector 8, after finite
capture-safe replacement and existential alpha conversion. This does not
construct a cut, suffix isomorphism, or addition output transport. -/
namespace PASoundness.PAtoCompactMemberTargetSuffixExists
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactMemberCutRawTargetIntro
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def original : Formula := .ex 34 suffixFormula
private def first : Formula := replace 32 8 original
private def suffixAt34 : Formula := replace 33 41 (replace 32 8 suffixFormula)
private theorem renamed_shape : replace 33 41 first = .ex 34 suffixAt34 := by decide

/-- Selector 8 supplies the literal K-negation filter of target 8 by cut 41. The
output binder is alpha-converted to 38; target and cut may denote the same
object. All substitutions are finite K proof transformations. -/
def target_suffix_exists : KDerivation (existsCode 38 targetSuffix.encode) := by
  have h0 : KDerivation original.encode := by
    simpa only [original,Formula.encode] using PAtoCompactAdditionSuffixClosed.suffix_exists
  have h1 : KDerivation first.encode :=
    replace_derivation 32 8 original (by decide) (by decide) h0
  have h2 := replace_derivation 33 41 first (by decide) (by decide) h1
  rw [renamed_shape] at h2
  have h34 : KDerivation (existsCode 34 suffixAt34.encode) := by
    simpa only [Formula.encode] using h2
  have ha := (existentialAlpha 34 38 suffixAt34 (by decide) (by decide) (by decide)).1
  have hf : replace 34 38 suffixAt34 = targetSuffix := by rfl
  rw [hf] at ha
  exact .mp h34 ha

theorem target_suffix_exists_certificate : theoremCode (certificate target_suffix_exists) =
    existsCode 38 targetSuffix.encode := certificate_correct target_suffix_exists
end PASoundness.PAtoCompactMemberTargetSuffixExists

#print axioms PASoundness.PAtoCompactMemberTargetSuffixExists.target_suffix_exists
#print axioms PASoundness.PAtoCompactMemberTargetSuffixExists.target_suffix_exists_certificate
