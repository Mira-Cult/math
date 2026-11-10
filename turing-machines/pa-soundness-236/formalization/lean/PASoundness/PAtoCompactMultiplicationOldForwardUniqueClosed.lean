import PASoundness.PAtoCompactMultiplicationOldForwardUniqueConditional
import PASoundness.PAtoCompactMultiplicationOldTripleRecover70
import PASoundness.PAtoCompactMultiplicationCleanOldTripleOutput70

/-! Concrete K transfer of old-coordinate product-output uniqueness to the
new graph. The old input, no-garbage row invariant, old graph cleanliness and
old uniqueness are explicit antecedents. This does not construct a graph or
prove a product or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationOldForwardUniqueClosed
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactMultiplicationOldForwardSpecialize
open PASoundness.PAtoCompactMultiplicationOldForwardUniqueConditional
open PASoundness.PAtoCompactMultiplicationOldTripleIntro
open PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha
open PASoundness.PAtoCompactMultiplicationOldTripleRecover70
open PASoundness.PAtoCompactMultiplicationCleanOldMemberOutput
open PASoundness.PAtoCompactMultiplicationCleanOldTripleOutput70
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The old-major query and the two graph invariants retained during transfer. -/
def hypotheses : Formula := namedBoth (.member 30 3)
  (namedBoth (noGarbage 64) oldClean)

private theorem query70_shape : replace 5 70 queriedTriple = tripleAt 64 70 := by decide
private theorem old70_shape : replace 5 70 oldTriple = tripleAt 10 70 := by decide

private def recovery : KDerivation (imp hypotheses.encode
    (imp (tripleAt 64 70).encode (tripleAt 10 70).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(tripleAt 64 70).encode,hypotheses.encode]
  have hq : Context Γ (tripleAt 64 70).encode := .head _ _
  have hh : Context Γ hypotheses.encode := .hypothesis (by simp [Γ])
  have hparts : Context Γ (both (member 30 3) (both (noGarbage 64).encode oldClean.encode)) := by
    simpa [hypotheses,namedBoth,Formula.not,Formula.encode,both,neg] using hh
  have ht : KDerivation (imp (member 30 3)
      (imp (noGarbage 64).encode (imp (tripleAt 64 70).encode (tripleAt 10 70).encode))) := by
    simpa [query70_shape,old70_shape] using recover_old_triple_70
  exact .mp hq (.mp (Context.conjunctionLeft (Context.conjunctionRight hparts))
    (.mp (Context.conjunctionLeft hparts) (.closed ht)))

private def output_bound : KDerivation (imp hypotheses.encode
    (imp (tripleAt 10 70).encode (member 32 70))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(tripleAt 10 70).encode,hypotheses.encode]
  have ht : Context Γ (tripleAt 10 70).encode := .head _ _
  have hh : Context Γ hypotheses.encode := .hypothesis (by simp [Γ])
  have hparts : Context Γ (both (member 30 3) (both (noGarbage 64).encode oldClean.encode)) := by
    simpa [hypotheses,namedBoth,Formula.not,Formula.encode,both,neg] using hh
  have ho : KDerivation (imp oldClean.encode (imp (tripleAt 10 70).encode (member 32 70))) := by
    simpa [old70_shape] using old_triple_output70
  exact .mp ht (.mp (Context.conjunctionRight (Context.conjunctionRight hparts)) (.closed ho))

/-- Existing old-coordinate uniqueness transfers to the new graph using
actual no-garbage recovery and clean-old output bounds, without assuming a
unique representation for nested pairs. -/
def unique_closed : KDerivation (imp hypotheses.encode (imp oldUnique.encode newUnique.encode)) :=
  unique_transfer hypotheses (hypotheses.vacuity 70 (by decide)) recovery output_bound

theorem unique_closed_certificate : theoremCode (certificate unique_closed) =
    imp hypotheses.encode (imp oldUnique.encode newUnique.encode) := certificate_correct unique_closed
end PASoundness.PAtoCompactMultiplicationOldForwardUniqueClosed
#print axioms PASoundness.PAtoCompactMultiplicationOldForwardUniqueClosed.unique_closed
#print axioms PASoundness.PAtoCompactMultiplicationOldForwardUniqueClosed.unique_closed_certificate
