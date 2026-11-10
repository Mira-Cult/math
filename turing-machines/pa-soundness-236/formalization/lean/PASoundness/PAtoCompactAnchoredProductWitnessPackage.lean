import PASoundness.PAtoCompactProductAllocatedCleanRowJoint
import PASoundness.PAtoCompactLiteralCutBaseSyntax
import PASoundness.PAtoCompactFilterInstantiation

/-! Package a supplied anchored-suffix existence proof with one clean old
product graph, one clean suffix map and its associated row graph. The suffix
existence proof remains an explicit input; no product successor matrix or
multiplication totality is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAnchoredProductWitnessPackage
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactLiteralCutBaseSyntax PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactProductCleanRowJoint PASoundness.PAtoCompactProductAllocatedCleanRowJoint
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Cut alternative, exact suffix filter and equivalence, at one suffix 40. -/
def suffixData : Formula := namedBoth (namedEither (.equal 32 45) (.member 45 32))
  (namedBoth (.all 35 (namedFilterBody 45 40 35 (Formula.member 32 35).not))
    (PAtoCompactOrdinalAddition.equivAt 31 40))

/-- Each nested graph uses the same cut and suffix. -/
def anchoredResult : Formula := .ex 40 (namedBoth suffixData jointResult)

def inputs : Formula := namedBoth (mulAt 100 30 31 32) (domainAt 100 31)

private theorem inputs_free40 : 40 ∉ inputs.free := by
  intro h
  have hh : 40 ∈ (mulAt 100 30 31 32).free ∨ 40 ∈ (domainAt 100 31).free := by
    simpa [inputs,namedBoth,Formula.not,Formula.free] using h
  rcases hh with hm | hd
  · have hm' := mulAt_free 100 30 31 32 hm
    simp at hm'
  · have hd' := domainAt_free 100 31 hd
    simp at hd'

/-- From an explicit K proof extracting a suffix, construct all graph
witnesses with that exact suffix. No independent graph or suffix choices can
be substituted afterward. -/
noncomputable def package_of_suffix
    (extract : KDerivation (imp (literalCutAt 100 32 31 45).encode
      (existsCode 40 suffixData.encode))) :
    KDerivation (imp (literalCutAt 100 32 31 45).encode
      (imp inputs.encode anchoredResult.encode)) := by
  have hpoint : KDerivation (imp inputs.encode
      (imp suffixData.encode (namedBoth suffixData jointResult).encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [suffixData.encode, inputs.encode]
    have hs : Context Γ suffixData.encode := .head _ _
    have hi : Context Γ (both (mulAt 100 30 31 32).encode (domainAt 100 31).encode) := by
      have hh : Context Γ inputs.encode := .hypothesis (by simp [Γ])
      simpa [inputs,namedBoth,Formula.not,Formula.encode,both,neg] using hh
    have he : Context Γ (PAtoCompactOrdinalAddition.equivAt 31 40).encode := by
      have hh : Context Γ (both (namedEither (.equal 32 45) (.member 45 32)).encode
          (both (Formula.all 35 (namedFilterBody 45 40 35 (Formula.member 32 35).not)).encode
            (PAtoCompactOrdinalAddition.equivAt 31 40).encode)) := by
        simpa [suffixData,namedBoth,Formula.not,Formula.encode,both,neg] using hs
      exact Context.conjunctionRight (Context.conjunctionRight hh)
    have hc : Context Γ (conditions 100).encode := by
      have hh := Context.conjunctionIntro (Context.conjunctionRight hi) he
      simpa [conditions,namedBoth,Formula.not,Formula.encode,both,neg] using hh
    have hj : Context Γ jointResult.encode :=
      .mp hc (.mp (Context.conjunctionLeft hi)
        (.closed (allocated_product_with_clean_suffix_and_row 100)))
    simpa [namedBoth,Formula.not,Formula.encode,both,neg] using Context.conjunctionIntro hs hj
  have hlift := conditionalExistsCongr 40 (free_vacuity 40 inputs inputs_free40) hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [inputs.encode,(literalCutAt 100 32 31 45).encode]
  have hi : Context Γ inputs.encode := .head _ _
  have hl : Context Γ (literalCutAt 100 32 31 45).encode := .hypothesis (by simp [Γ])
  have hs : Context Γ (existsCode 40 suffixData.encode) := .mp hl (.closed extract)
  have hr := Context.mp hs (Context.mp hi (.closed hlift))
  simpa [anchoredResult,Formula.encode] using hr
end PASoundness.PAtoCompactAnchoredProductWitnessPackage
#print axioms PASoundness.PAtoCompactAnchoredProductWitnessPackage.package_of_suffix
