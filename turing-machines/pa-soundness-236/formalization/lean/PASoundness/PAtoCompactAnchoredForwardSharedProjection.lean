import PASoundness.PAtoCompactAnchoredLexSharedProjection
import PASoundness.PAtoCompactMultiplicationForwardSharedContext

/-! A literal K projection from the components of one scoped anchored
product witness to the forward proof's shared context. It keeps the same old
graph 10, suffix map 6, row graph 64 and suffix 40. It does not eliminate the
witnesses, prove a product matrix, or establish multiplication totality. -/
namespace PASoundness.PAtoCompactAnchoredForwardSharedProjection
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactAnchoredProductWitnessPackage PASoundness.PAtoCompactCleanSuffixRowPackage
open PASoundness.PAtoCompactAnchoredLexSharedProjection
open PASoundness.PAtoCompactMultiplicationLexSharedContext
open PASoundness.PAtoCompactFixedFirstRowGraph64 PASoundness.PAtoCompactFixedFirstRowSuffixTarget40
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The component hypotheses retain the same free witness names throughout.
The map-bijection follows from that very clean suffix matrix; no second map is
selected. -/
def forward_from_components : KDerivation
    (imp (domainAt 100 30).encode (imp (domainAt 100 32).encode
      (imp (domainAt 100 45).encode (imp suffixData.encode
        (imp oldBody.encode (imp cleanMatrix.encode (imp rowBody64.encode
          (imp (successorCode 30 38 39)
            PASoundness.PAtoCompactMultiplicationForwardSharedContext.context.encode)))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [successorCode 30 38 39,rowBody64.encode,cleanMatrix.encode,oldBody.encode,
    suffixData.encode,(domainAt 100 45).encode,(domainAt 100 32).encode,(domainAt 100 30).encode]
  have hs : Context Γ (successorCode 30 38 39) := .head _ _
  have hr : Context Γ rowBody64.encode := .hypothesis (by simp [Γ])
  have hc : Context Γ cleanMatrix.encode := .hypothesis (by simp [Γ])
  have ho : Context Γ oldBody.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ suffixData.encode := .hypothesis (by simp [Γ])
  have h45 : Context Γ (domainAt 100 45).encode := .hypothesis (by simp [Γ])
  have h32 : Context Γ (domainAt 100 32).encode := .hypothesis (by simp [Γ])
  have h30 : Context Γ (domainAt 100 30).encode := .hypothesis (by simp [Γ])
  have hshared : Context Γ sharedPremise.encode :=
    .mp hc (.mp ho (.mp hf (.mp h45 (.mp h32 (.mp h30 (.closed shared_from_components))))))
  have hp : Context Γ (both (both suffixBijection.encode suffixOrder.encode)
      PASoundness.PAtoCompactMultiplicationSuffixCleanEdges.suffixClean.encode) := by
    simpa [cleanMatrix,namedBoth,Formula.not,Formula.encode,both,neg] using hc
  have hmap : Context Γ mapBijection40.encode := by
    have hh := Context.conjunctionLeft (Context.conjunctionLeft hp)
    simpa [suffixBijection,mapBijection40] using hh
  have hresult := Context.conjunctionIntro hshared
    (Context.conjunctionIntro hmap (Context.conjunctionIntro hr hs))
  change Context Γ PASoundness.PAtoCompactMultiplicationForwardSharedContext.context.encode
  simpa [PASoundness.PAtoCompactMultiplicationForwardSharedContext.context,
    namedBoth,namedSuccessor,namedSuccessorBody,namedEither,Formula.not,
    Formula.encode,successorCode,both,neg,either] using hresult

theorem forward_from_components_certificate :
    theoremCode (certificate forward_from_components) =
      imp (domainAt 100 30).encode (imp (domainAt 100 32).encode
        (imp (domainAt 100 45).encode (imp suffixData.encode
          (imp oldBody.encode (imp cleanMatrix.encode (imp rowBody64.encode
            (imp (successorCode 30 38 39)
              PASoundness.PAtoCompactMultiplicationForwardSharedContext.context.encode))))))) :=
  certificate_correct _
end PASoundness.PAtoCompactAnchoredForwardSharedProjection
#print axioms PASoundness.PAtoCompactAnchoredForwardSharedProjection.forward_from_components
#print axioms PASoundness.PAtoCompactAnchoredForwardSharedProjection.forward_from_components_certificate
