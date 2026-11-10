import PASoundness.PAtoCompactAnchoredProductWitnessPackage
import PASoundness.PAtoCompactMultiplicationLexSharedContext

/-! Assemble the actual multiplication lexicographic shared assumptions from
literal scoped witness components and explicit candidate guards. This finite K
proof does not eliminate existential witnesses, establish a product matrix,
or assert multiplication totality or PA soundness. -/
namespace PASoundness.PAtoCompactAnchoredLexSharedProjection
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactAnchoredProductWitnessPackage PASoundness.PAtoCompactCleanSuffixRowPackage
open PASoundness.PAtoCompactMultiplicationLexSharedContext
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The exact old-matrix/cleanliness conjunction from the jointly scoped
witness, at old graph label 10. -/
def oldBody : Formula := namedBoth
  PASoundness.PAtoCompactProductCleanRebased303132.oldMatrixActual
  PASoundness.PAtoCompactProductCleanRebased303132.oldCleanActual

/-- All hypotheses are literal K antecedents; graph labels 10 and 6 refer to
the same old and suffix-map witnesses carried by the surrounding package. -/
def shared_from_components : KDerivation
    (imp (domainAt 100 30).encode (imp (domainAt 100 32).encode
      (imp (domainAt 100 45).encode (imp suffixData.encode
        (imp oldBody.encode (imp cleanMatrix.encode sharedPremise.encode)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [cleanMatrix.encode,oldBody.encode,suffixData.encode,
    (domainAt 100 45).encode,(domainAt 100 32).encode,(domainAt 100 30).encode]
  have hclean : Context Γ cleanMatrix.encode := .head _ _
  have hold : Context Γ oldBody.encode := .hypothesis (by simp [Γ])
  have hsuffix : Context Γ suffixData.encode := .hypothesis (by simp [Γ])
  have h45 : Context Γ (domainAt 100 45).encode := .hypothesis (by simp [Γ])
  have h32 : Context Γ (domainAt 100 32).encode := .hypothesis (by simp [Γ])
  have h30 : Context Γ (domainAt 100 30).encode := .hypothesis (by simp [Γ])
  have hold' : Context Γ (both oldMatrixActual.encode oldCleanActual.encode) := by
    simpa [oldBody,namedBoth,Formula.not,Formula.encode,both,neg,
      PASoundness.PAtoCompactProductCleanRebased303132.oldMatrixActual,
      PASoundness.PAtoCompactProductCleanRebased303132.oldCleanActual,
      oldMatrixActual,oldCleanActual] using hold
  have hsuffix' : Context Γ (both cutAlternative.encode
      (both suffixFilter.encode (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 40).encode)) := by
    simpa [suffixData,cutAlternative,suffixFilter,namedBoth,Formula.not,Formula.encode,both,neg] using hsuffix
  have hclean' : Context Γ (both (both suffixBijection.encode
      PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder.suffixOrder.encode)
      PASoundness.PAtoCompactMultiplicationSuffixCleanEdges.suffixClean.encode) := by
    simpa [cleanMatrix,suffixOrder,
      PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder.suffixOrder,
      namedBoth,Formula.not,Formula.encode,both,neg] using hclean
  have hres := Context.conjunctionIntro (Context.conjunctionLeft hold')
    (Context.conjunctionIntro (Context.conjunctionRight hold')
      (Context.conjunctionIntro h45 (Context.conjunctionIntro h32 (Context.conjunctionIntro h30
        (Context.conjunctionIntro (Context.conjunctionLeft hsuffix')
          (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight hsuffix'))
            (Context.conjunctionIntro (Context.conjunctionRight (Context.conjunctionLeft hclean'))
              (Context.conjunctionRight hclean'))))))))
  simpa [sharedPremise,namedBoth,Formula.not,Formula.encode,both,neg] using hres

theorem shared_from_components_certificate :
    theoremCode (certificate shared_from_components) =
      imp (domainAt 100 30).encode (imp (domainAt 100 32).encode
        (imp (domainAt 100 45).encode (imp suffixData.encode
          (imp oldBody.encode (imp cleanMatrix.encode sharedPremise.encode))))) :=
  certificate_correct _
end PASoundness.PAtoCompactAnchoredLexSharedProjection
#print axioms PASoundness.PAtoCompactAnchoredLexSharedProjection.shared_from_components
#print axioms PASoundness.PAtoCompactAnchoredLexSharedProjection.shared_from_components_certificate
