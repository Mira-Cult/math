import PASoundness.PAtoCompactOrdinalAddition
import PASoundness.CompactQuantifiers
import PASoundness.PAtoCompactZeroSuccessor

/-! Introduce a supplied target member cut and suffix into the literal target
addition. This syntax-level step assumes all quotient and suffix facts; it
does not construct them or establish output transport. -/
namespace PASoundness.PAtoCompactMemberCutRawTargetIntro
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrdinalAddition
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def targetAddition : Formula := replace 32 8 additionFormula
def targetCutEquivalence : Formula := replace 33 41 (equivAt 30 33)
def targetSuffix : Formula := replace 34 38 (replace 33 41 (replace 32 8 suffixFormula))
def targetSuffixEquivalence : Formula := replace 34 38 (equivAt 31 34)
def targetRelation : Formula := namedEither (.equal 41 8) (.member 8 41)
def targetBody : Formula := namedBoth targetRelation (namedBoth targetCutEquivalence
  (namedBoth targetSuffix targetSuffixEquivalence))
def allocatedTarget : Formula := .ex 41 (.ex 38 targetBody)

private def rawBody : Formula := namedBoth (namedEither (.equal 33 32) (.member 32 33))
  (namedBoth (equivAt 30 33) (namedBoth suffixFormula (equivAt 31 34)))
private def instantiatedBody : Formula := replace 32 8 rawBody
private def cutBody : Formula := replace 33 41 instantiatedBody
private theorem target_shape : targetAddition = .ex 33 (.ex 34 instantiatedBody) := by decide
private theorem cut_shape : replace 33 41 (.ex 34 instantiatedBody) = .ex 34 cutBody := by decide
private theorem body_shape : replace 34 38 cutBody = targetBody := by decide

/-- Reverse the two capture-safe existential alpha conversions. -/
def allocated_to_target : KDerivation (imp allocatedTarget.encode targetAddition.encode) := by
  have hcut := (existentialAlpha 33 41 (.ex 34 instantiatedBody) (by decide) (by decide) (by decide)).2
  rw [cut_shape] at hcut
  have hsuffix := (existentialAlpha 34 38 cutBody (by decide) (by decide) (by decide)).2
  rw [body_shape] at hsuffix
  have h := compose (existsCongr 41 hsuffix) hcut
  rw [target_shape]
  simpa only [allocatedTarget,Formula.encode] using h

/-- A target member cut, first-to-cut equivalence, target suffix, and
second-to-suffix equivalence give the literal target addition. The same cut41
and suffix38 are introduced as witnesses; represented values may coincide. -/
def target_from_member_cut : KDerivation
    (imp (member 8 41) (imp targetCutEquivalence.encode
      (imp targetSuffix.encode (imp targetSuffixEquivalence.encode targetAddition.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [targetSuffixEquivalence.encode,targetSuffix.encode,targetCutEquivalence.encode,member 8 41]
  have he : Context Γ targetSuffixEquivalence.encode := .head _ _
  have hf : Context Γ targetSuffix.encode := .hypothesis (by simp [Γ])
  have hc : Context Γ targetCutEquivalence.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 8 41) := .hypothesis (by simp [Γ])
  have hr : Context Γ targetRelation.encode := by
    have h := Context.disjunctionRight (a := equal 41 8) hm
    simpa [targetRelation,namedEither,Formula.not,Formula.encode,either,neg] using h
  have hbody : Context Γ targetBody.encode := by
    have h := Context.conjunctionIntro hr (Context.conjunctionIntro hc
      (Context.conjunctionIntro hf he))
    simpa [targetBody,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have hs : Context Γ (existsCode 38 targetBody.encode) :=
    .mp hbody (.closed (existsIntroduce 38 targetBody (by decide)))
  have hc' : Context Γ allocatedTarget.encode := by
    have hi := existsIntroduce 41 (.ex 38 targetBody) (by decide)
    have h := Context.mp hs (.closed hi)
    simpa only [allocatedTarget,Formula.encode] using h
  exact .mp hc' (.closed allocated_to_target)

theorem allocated_to_target_certificate : theoremCode (certificate allocated_to_target) =
    imp allocatedTarget.encode targetAddition.encode := certificate_correct allocated_to_target

theorem target_from_member_cut_certificate : theoremCode (certificate target_from_member_cut) =
    imp (member 8 41) (imp targetCutEquivalence.encode
      (imp targetSuffix.encode (imp targetSuffixEquivalence.encode targetAddition.encode))) :=
  certificate_correct target_from_member_cut
end PASoundness.PAtoCompactMemberCutRawTargetIntro

#print axioms PASoundness.PAtoCompactMemberCutRawTargetIntro.allocated_to_target
#print axioms PASoundness.PAtoCompactMemberCutRawTargetIntro.target_from_member_cut
#print axioms PASoundness.PAtoCompactMemberCutRawTargetIntro.allocated_to_target_certificate
#print axioms PASoundness.PAtoCompactMemberCutRawTargetIntro.target_from_member_cut_certificate
