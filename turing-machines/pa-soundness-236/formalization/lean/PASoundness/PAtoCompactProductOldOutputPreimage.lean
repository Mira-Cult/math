import PASoundness.PAtoCompactProductOldTriplePreserved
import PASoundness.PAtoCompactTransitiveClosure
import PASoundness.PAtoCompactAdjunction
import PASoundness.CompactQuantifiers

/-! A K witness transfer for an old-output point in a proposed multiplication
successor graph. It keeps the actual nested-pair and original uniqueness
witnesses, but it does not prove uniqueness against newly added graph edges,
the full reverse clause, or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOldOutputPreimage
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductOldTriplePreserved
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The old reverse clause at first factor 30, second factor 31, result 32,
and old graph 10. Names are syntactic; their denoted values may coincide. -/
def oldReverse : Formula :=
  replace 6 10 (replace 2 32 (replace 1 31 (replace 0 30 reverseFormula)))
private def inclusion : Formula := .all 9 (.imp (.member 10 9) (.member 64 9))
private def triple (g a b c : Nat) : Formula := .ex 18
  (namedBoth (pairFormula 18 a b) (graphFormula g 18 c))
private def oldUnique : Formula := .all 7 (.all 8
  (.imp (namedBoth (.member 30 7) (namedBoth (.member 31 8) (triple 10 7 8 5)))
    (namedBoth (.equal 7 3) (.equal 8 4))))
private def oldBody : Formula := namedBoth (.member 30 3)
  (namedBoth (.member 31 4) (namedBoth (triple 10 3 4 5) oldUnique))
/-- New graph 64 retains an old output preimage and the original uniqueness
against old-graph competitors. Uniqueness against new edges is not asserted. -/
def retainedBody : Formula := namedBoth (.member 38 3)
  (namedBoth (.member 31 4) (namedBoth (triple 64 3 4 5) oldUnique))
private def newWitness : Formula := .ex 3 (.ex 4 retainedBody)
private def oldWitness : Formula := .ex 3 (.ex 4 oldBody)
private def premises : Formula := namedBoth inclusion (namedSuccessor 30 38 39)

private theorem oldReverse_shape : oldReverse =
    .all 5 (.imp (.member 32 5) oldWitness) := by decide

/-- At output name 5, the old reverse clause provides its original two
preimages and its old-graph uniqueness clause. -/
def old_preimage : KDerivation (imp oldReverse.encode
    (imp (member 32 5) oldWitness.encode)) := by
  rw [oldReverse_shape]
  have h := allSpecialize 5 (.imp (.member 32 5) oldWitness) (by decide)
  simpa [Formula.encode] using h

private def body_transfer : KDerivation (imp premises.encode
    (imp oldBody.encode retainedBody.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldBody.encode,premises.encode]
  have hw : Context Γ oldBody.encode := .head _ _
  have hp : Context Γ premises.encode := .hypothesis (by simp [Γ])
  have hp' : Context Γ (both inclusion.encode (successorCode 30 38 39)) := by
    simpa [premises,namedBoth,namedSuccessor,namedSuccessorBody,namedEither,
      Formula.encode,Formula.not,successorCode,both,neg,either] using hp
  have hincl : Context Γ inclusion.encode := Context.conjunctionLeft hp'
  have hsucc : Context Γ (successorCode 30 38 39) := Context.conjunctionRight hp'
  have hw' : Context Γ (both (member 30 3)
      (both (member 31 4) (both (triple 10 3 4 5).encode oldUnique.encode))) := by
    simpa [oldBody,namedBoth,Formula.encode,both,neg] using hw
  have hfirst : Context Γ (member 30 3) := Context.conjunctionLeft hw'
  have hsecond : Context Γ (member 31 4) := Context.conjunctionLeft (Context.conjunctionRight hw')
  have hedge : Context Γ (triple 10 3 4 5).encode :=
    Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hw'))
  have hu : Context Γ oldUnique.encode :=
    Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hw'))
  have hfirst' : Context Γ (member 38 3) :=
    .mp (Context.disjunctionRight hfirst) (.mp hsucc (.closed (successor_include 30 38 39 3 (by decide) (by decide) (by decide))))
  have hedge' : Context Γ (triple 64 3 4 5).encode := by
    apply Context.mp hedge
    apply Context.mp hincl
    exact .closed triple_preserved
  simpa [retainedBody,namedBoth,Formula.encode,both,neg] using
    Context.conjunctionIntro hfirst' (Context.conjunctionIntro hsecond (Context.conjunctionIntro hedge' hu))

/-- An old output retains a preimage in the extended graph, with the old
uniqueness condition kept intact. Full new-graph uniqueness remains separate. -/
def old_output_preimage : KDerivation (imp inclusion.encode
    (imp (successorCode 30 38 39) (imp oldReverse.encode
      (imp (member 32 5) newWitness.encode)))) := by
  have hp4 := conditionalExistsCongr 4 (premises.vacuity 4 (by decide)) body_transfer
  have hp3 := conditionalExistsCongr 3 (premises.vacuity 3 (by decide)) hp4
  have hmap : KDerivation (imp premises.encode (imp oldWitness.encode newWitness.encode)) := by
    simpa [oldWitness,newWitness,Formula.encode] using hp3
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 32 5,oldReverse.encode,successorCode 30 38 39,inclusion.encode]
  have hz : Context Γ (member 32 5) := .head _ _
  have hr : Context Γ oldReverse.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode 30 38 39) := .hypothesis (by simp [Γ])
  have hi : Context Γ inclusion.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ premises.encode := by
    simpa [premises,namedBoth,namedSuccessor,namedSuccessorBody,namedEither,
      Formula.encode,Formula.not,successorCode,both,neg,either] using Context.conjunctionIntro hi hs
  have ho : Context Γ oldWitness.encode := .mp hz (.mp hr (.closed old_preimage))
  exact .mp ho (.mp hp (.closed hmap))

theorem old_output_preimage_certificate : theoremCode (certificate old_output_preimage) =
    imp inclusion.encode (imp (successorCode 30 38 39) (imp oldReverse.encode
      (imp (member 32 5) newWitness.encode))) := certificate_correct old_output_preimage
end PASoundness.PAtoCompactProductOldOutputPreimage
#print axioms PASoundness.PAtoCompactProductOldOutputPreimage.old_preimage
#print axioms PASoundness.PAtoCompactProductOldOutputPreimage.old_output_preimage
#print axioms PASoundness.PAtoCompactProductOldOutputPreimage.old_output_preimage_certificate
