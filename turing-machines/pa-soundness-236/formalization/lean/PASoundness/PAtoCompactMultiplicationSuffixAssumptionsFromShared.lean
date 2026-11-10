import PASoundness.PAtoCompactMultiplicationForwardSharedContext
import PASoundness.PAtoCompactMultiplicationSuffixRowPreimageRetained
import PASoundness.PAtoCompactMultiplicationSuffixCompetitorClosed

/-! Derive the explicit suffix-competitor assumptions from the shared product
context, suffix membership, and the same retained row preimage. This is a
finite K projection, not a reverse product clause or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationSuffixAssumptionsFromShared
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder
open PASoundness.PAtoCompactFixedFirstRowSuffixTarget40
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFixedFirstPreservedBase PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactFixedFirstRowGraph64
open PASoundness.PAtoCompactMultiplicationLexSharedContext PASoundness.PAtoCompactMultiplicationForwardSharedContext
open PASoundness.PAtoCompactMultiplicationSuffixRowPreimageRetained
open PASoundness.PAtoCompactMultiplicationSuffixCompetitorClosed
open PASoundness.PAtoCompactProductOldSuffixExclusion PASoundness.PAtoCompactMultiplicationFullPrefixOldEdge
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges PASoundness.PAtoCompactMultiplicationSuffixInjective41
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Common product context together with membership of output 5 in the suffix. -/
def suffixContext : Formula := namedBoth context (.member 40 5)

private theorem clean_alignment : oldCleanActual = oldClean := by decide
private theorem row_shape : rowBody64 = namedBoth (replace 0 31 (oldPreserved 64))
    (namedBoth (replace 0 31 (coverage 64)) fullNoGarbage) := by decide
private theorem bijection_alignment : mapBijection40 = suffixBijection := by decide

/-- The shared assumptions and an actual retained row preimage furnish all
conditions used by the suffix competitor theorem, preserving the same F-edge
from chosen minor 41 to output 5. -/
def assumptions_from_shared : KDerivation (imp suffixContext.encode
    (imp rowPreimageBody.encode assumptions.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [rowPreimageBody.encode,suffixContext.encode]
  have hp : Context Γ (both (member 31 41) (both (graphFormula 6 41 5).encode
      (both (pairFormula 12 30 41).encode (graphFormula 64 12 5).encode))) := by
    have h : Context Γ rowPreimageBody.encode := .head _ _
    simpa [rowPreimageBody,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have hc : Context Γ (both context.encode (member 40 5)) := by
    have h : Context Γ suffixContext.encode := .hypothesis (by simp [Γ])
    simpa [suffixContext,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have hcontext := Context.conjunctionLeft hc
  have hmember := Context.conjunctionRight hc
  have hshared : Context Γ sharedPremise.encode := .mp hcontext (.closed project_shared)
  have hrow : Context Γ rowBody64.encode := .mp hcontext (.closed project_row)
  have hmap : Context Γ mapBijection40.encode := .mp hcontext (.closed project_map)
  have hparts : Context Γ (both oldMatrixActual.encode
      (both oldCleanActual.encode (both (domainAt 100 45).encode (both (domainAt 100 32).encode
        (both (domainAt 100 30).encode (both cutAlternative.encode
          (both suffixFilter.encode (both suffixOrder.encode suffixClean.encode)))))))) := by
    simpa [sharedPremise,namedBoth,Formula.not,Formula.encode,both,neg] using hshared
  have hold' := Context.conjunctionLeft (Context.conjunctionRight hparts)
  have hold : Context Γ oldClean.encode := by simpa only [clean_alignment] using hold'
  have hrest := Context.conjunctionRight (Context.conjunctionRight hparts)
  have hfilter : Context Γ suffixFilter.encode := Context.conjunctionLeft
    (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight
      (Context.conjunctionRight hrest))))
  have hfc : Context Γ suffixClean.encode := Context.conjunctionRight
    (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight
      (Context.conjunctionRight (Context.conjunctionRight hrest)))))
  have hr : Context Γ (both (replace 0 31 (oldPreserved 64)).encode
      (both (replace 0 31 (coverage 64)).encode fullNoGarbage.encode)) := by
    rw [row_shape] at hrow
    simpa [namedBoth,Formula.not,Formula.encode,both,neg] using hrow
  have hng : Context Γ fullNoGarbage.encode := Context.conjunctionRight (Context.conjunctionRight hr)
  have hb : Context Γ suffixBijection.encode := by simpa only [bijection_alignment] using hmap
  have hedge : Context Γ (graphFormula 6 41 5).encode := Context.conjunctionLeft (Context.conjunctionRight hp)
  have hall := Context.conjunctionIntro hng (Context.conjunctionIntro hold
    (Context.conjunctionIntro hfilter (Context.conjunctionIntro hmember
      (Context.conjunctionIntro hfc (Context.conjunctionIntro hb hedge)))))
  change Context Γ (both fullNoGarbage.encode (both oldClean.encode
    (both suffixFilter.encode (both (member 40 5)
      (both suffixClean.encode (both suffixBijection.encode (graphFormula 6 41 5).encode))))))
  exact hall

theorem assumptions_from_shared_certificate : theoremCode (certificate assumptions_from_shared) =
    imp suffixContext.encode (imp rowPreimageBody.encode assumptions.encode) :=
  certificate_correct assumptions_from_shared
end PASoundness.PAtoCompactMultiplicationSuffixAssumptionsFromShared
#print axioms PASoundness.PAtoCompactMultiplicationSuffixAssumptionsFromShared.assumptions_from_shared
#print axioms PASoundness.PAtoCompactMultiplicationSuffixAssumptionsFromShared.assumptions_from_shared_certificate
