import PASoundness.PAtoCompactMultiplicationFixedRowReverseWitness
import PASoundness.PAtoCompactMultiplicationSuffixFixedUnique
import PASoundness.PAtoCompactMultiplicationSuffixAssumptionsFromShared
import PASoundness.PAtoCompactMultiplicationReverseContextProjections

/-! The suffix branch of the product reverse clause for the common named
product-successor context. The proof preserves the same clean suffix-map,
row graph, and pair witnesses, quantifies uniqueness at the selected 30/41
coordinates, then introduces the reverse-clause names. This does not establish
the old-output branch, the complete product matrix or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationSuffixReverseCaseFixed
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFixedFirstPreservedBase
open PASoundness.PAtoCompactFixedFirstRowGraph64
open PASoundness.PAtoCompactMultiplicationForwardSharedContext
open PASoundness.PAtoCompactMultiplicationReverseContextProjections
open PASoundness.PAtoCompactMultiplicationSuffixPreimageFive (suffixBijection)
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges (suffixClean)
open PASoundness.PAtoCompactMultiplicationSuffixRowPreimageRetained (rowPreimage rowPreimageBody suffix_row_preimage_retained)
open PASoundness.PAtoCompactMultiplicationSuffixAssumptionsFromShared
open PASoundness.PAtoCompactMultiplicationSuffixFixedUnique (fixed_unique_of_assumptions)
open PASoundness.PAtoCompactMultiplicationFixedRowReverseWitness (reverse_from_fixed_row)
open PASoundness.PAtoCompactMultiplicationReverseWitnessFromPoint (targetBody)
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private theorem suffix_free12 : 12 ∉ suffixContext.free := by
  simp [suffixContext,namedBoth,Formula.free,context_free]
private theorem suffix_free41 : 41 ∉ suffixContext.free := by
  simp [suffixContext,namedBoth,Formula.free,context_free]

private def suffix_context_successor : KDerivation
    (imp suffixContext.encode (successorCode 30 38 39)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [suffixContext.encode]
  have hc : Context Γ (both context.encode (member 40 5)) := by
    have h : Context Γ suffixContext.encode := .head _ _
    simpa [suffixContext,namedBoth,Formula.not,Formula.encode,both,neg] using h
  exact .mp (Context.conjunctionLeft hc) (.closed project_successor)

private def suffix_context_unique : KDerivation (imp suffixContext.encode
    (imp rowPreimageBody.encode PAtoCompactMultiplicationFixedRowReverseWitness.fixedUnique.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [rowPreimageBody.encode,suffixContext.encode]
  have hr : Context Γ rowPreimageBody.encode := .head _ _
  have hc : Context Γ suffixContext.encode := .hypothesis (by simp [Γ])
  have ha := Context.mp hr (Context.mp hc (.closed assumptions_from_shared))
  have hu := Context.mp ha (.closed fixed_unique_of_assumptions)
  exact hu

/-- Given the common product context and a member of the suffix, there is an
exact reverse-clause preimage with both competitor uniqueness conjuncts. The
major witness is 30, the minor witness is the retained suffix-map source 41,
and no equality of pair representatives is assumed. -/
def suffix_case : KDerivation (imp context.encode (imp (member 40 5)
    (existsCode 3 (existsCode 4 targetBody.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 40 5,context.encode]
  have hm : Context Γ (member 40 5) := .head _ _
  have hh : Context Γ context.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ suffixBijection.encode := .mp hh (.closed project_suffixBijection)
  have hc : Context Γ suffixClean.encode := .mp hh (.closed project_suffixClean)
  have hr : Context Γ (replace 0 31 (rowInvariantPreserved 64)).encode := by
    have h := Context.mp hh (.closed project_row)
    simpa only [row_body64_shape] using h
  have he : Context Γ rowPreimage.encode :=
    .mp hm (.mp hr (.mp hc (.mp hb (.closed suffix_row_preimage_retained))))
  have hsc : Context Γ suffixContext.encode := by
    simpa [suffixContext,namedBoth,Formula.not,Formula.encode,both,neg] using
      Context.conjunctionIntro hh hm
  exact .mp he (.mp hsc (.closed (reverse_from_fixed_row suffixContext suffix_free12 suffix_free41
    suffix_context_successor suffix_context_unique)))

theorem suffix_case_certificate : theoremCode (certificate suffix_case) =
    imp context.encode (imp (member 40 5) (existsCode 3 (existsCode 4 targetBody.encode))) :=
  certificate_correct suffix_case
end PASoundness.PAtoCompactMultiplicationSuffixReverseCaseFixed
#print axioms PASoundness.PAtoCompactMultiplicationSuffixReverseCaseFixed.suffix_case
#print axioms PASoundness.PAtoCompactMultiplicationSuffixReverseCaseFixed.suffix_case_certificate
