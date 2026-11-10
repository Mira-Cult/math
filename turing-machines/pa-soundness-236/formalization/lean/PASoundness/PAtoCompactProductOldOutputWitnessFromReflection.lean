import PASoundness.PAtoCompactProductOldOutputPreimage
import PASoundness.PAtoCompactProductOldReverseUniqueTransfer

/-! Conditional K witness construction for an old output in an extended
multiplication graph. It keeps the same source witnesses and derives
uniqueness against new-graph competitors from a supplied K reflection proof.
The reflection, graph extension, and product-totality proofs remain open. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOldOutputWitnessFromReflection
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactProductOldOutputPreimage
open PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductOldReverseUniqueTransfer
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def inclusion : Formula := .all 9 (.imp (.member 10 9) (.member 64 9))
private def triple (g a b c : Nat) : Formula := .ex 18
  (namedBoth (pairFormula 18 a b) (graphFormula g 18 c))
/-- The same preimage witnesses with uniqueness against the entire new graph. -/
def targetBody : Formula := namedBoth (.member 38 3)
  (namedBoth (.member 31 4) (namedBoth (triple 64 3 4 5) newUnique))
/-- The existential preimage and new-graph uniqueness, at fixed output name 5. -/
def targetWitness : Formula := .ex 3 (.ex 4 targetBody)

/-- The witness is exactly the body of the literal product reverse clause
for new factors 38,31, result 45, and graph 64. -/
theorem target_witness_shape :
    replace 6 64 (replace 2 45 (replace 1 31 (replace 0 38 reverseFormula))) =
      .all 5 (.imp (.member 45 5) targetWitness) := by decide

private def upgrade_body (G : Formula)
    (hG7 : KDerivation (imp G.encode (allCode 7 G.encode)))
    (hG8 : KDerivation (imp G.encode (allCode 8 G.encode)))
    (reflect : KDerivation (imp G.encode (imp (member 38 7) (imp (member 31 8)
      (imp (competitorTriple 64).encode
        (both (member 30 7) (competitorTriple 10).encode)))))) :
    KDerivation (imp G.encode (imp retainedBody.encode targetBody.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [retainedBody.encode, G.encode]
  have hg : Context Γ G.encode := .hypothesis (by simp [Γ])
  have hbody : Context Γ (both (member 38 3)
      (both (member 31 4) (both (triple 64 3 4 5).encode oldUnique.encode))) := by
    have h : Context Γ retainedBody.encode := .head _ _
    change Context Γ (both (member 38 3)
      (both (member 31 4) (both (triple 64 3 4 5).encode oldUnique.encode))) at h
    exact h
  have ha := Context.conjunctionLeft hbody
  have hb := Context.conjunctionLeft (Context.conjunctionRight hbody)
  have ht := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hbody))
  have hu := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hbody))
  have hu' : Context Γ newUnique.encode := .mp hu (.mp hg (.closed (unique_from_reflection G hG7 hG8 reflect)))
  change Context Γ (both (member 38 3)
    (both (member 31 4) (both (triple 64 3 4 5).encode newUnique.encode)))
  exact Context.conjunctionIntro ha (Context.conjunctionIntro hb (Context.conjunctionIntro ht hu'))

/-- From the explicit guard and reflection proof, the old-output preimage is
unique against the new graph. The guard must be vacuous at witness names 3,4
and competitor names 7,8. No graph reflection is inferred from soundness. -/
def old_output_unique_from_reflection (G : Formula)
    (hG3 : KDerivation (imp G.encode (allCode 3 G.encode)))
    (hG4 : KDerivation (imp G.encode (allCode 4 G.encode)))
    (hG7 : KDerivation (imp G.encode (allCode 7 G.encode)))
    (hG8 : KDerivation (imp G.encode (allCode 8 G.encode)))
    (reflect : KDerivation (imp G.encode (imp (member 38 7) (imp (member 31 8)
      (imp (competitorTriple 64).encode
        (both (member 30 7) (competitorTriple 10).encode)))))) :
    KDerivation (imp G.encode (imp inclusion.encode
      (imp (successorCode 30 38 39) (imp oldReverse.encode
        (imp (member 32 5) targetWitness.encode))))) := by
  have h4 := conditionalExistsCongr 4 hG4 (upgrade_body G hG7 hG8 reflect)
  have h3 := conditionalExistsCongr 3 hG3 h4
  have hmap : KDerivation (imp G.encode
      (imp (Formula.ex 3 (.ex 4 retainedBody)).encode targetWitness.encode)) := by
    simpa [targetWitness, Formula.encode] using h3
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 32 5, oldReverse.encode, successorCode 30 38 39,
    inclusion.encode, G.encode]
  have hz : Context Γ (member 32 5) := .head _ _
  have hr : Context Γ oldReverse.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode 30 38 39) := .hypothesis (by simp [Γ])
  have hi : Context Γ inclusion.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ G.encode := .hypothesis (by simp [Γ])
  have hw : Context Γ (Formula.ex 3 (.ex 4 retainedBody)).encode := by
    apply Context.mp hz
    apply Context.mp hr
    apply Context.mp hs
    apply Context.mp hi
    exact .closed old_output_preimage
  exact .mp hw (.mp hg (.closed hmap))

theorem old_output_unique_from_reflection_certificate (G : Formula)
    (hG3 : KDerivation (imp G.encode (allCode 3 G.encode)))
    (hG4 : KDerivation (imp G.encode (allCode 4 G.encode)))
    (hG7 : KDerivation (imp G.encode (allCode 7 G.encode)))
    (hG8 : KDerivation (imp G.encode (allCode 8 G.encode)))
    (reflect : KDerivation (imp G.encode (imp (member 38 7) (imp (member 31 8)
      (imp (competitorTriple 64).encode
        (both (member 30 7) (competitorTriple 10).encode)))))) :
    theoremCode (certificate (old_output_unique_from_reflection G hG3 hG4 hG7 hG8 reflect)) =
      imp G.encode (imp inclusion.encode (imp (successorCode 30 38 39)
        (imp oldReverse.encode (imp (member 32 5) targetWitness.encode)))) :=
  certificate_correct (old_output_unique_from_reflection G hG3 hG4 hG7 hG8 reflect)
end PASoundness.PAtoCompactProductOldOutputWitnessFromReflection
#print axioms PASoundness.PAtoCompactProductOldOutputWitnessFromReflection.target_witness_shape
#print axioms PASoundness.PAtoCompactProductOldOutputWitnessFromReflection.old_output_unique_from_reflection
#print axioms PASoundness.PAtoCompactProductOldOutputWitnessFromReflection.old_output_unique_from_reflection_certificate
