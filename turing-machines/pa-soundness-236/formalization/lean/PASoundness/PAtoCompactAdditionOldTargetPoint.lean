import PASoundness.PAtoCompactAdditionSuccessorGraphClean

/-! One old-target uniqueness step for the distinct-top addition graph.
The old-edge guard, old uniqueness, new-edge split and old target membership
are explicit hypotheses. The suffix filter excludes the newly adjoined target
without requiring suffix transitivity. This is not a full bijection or an
addition totality theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionOldTargetPoint
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactAdditionSuccessorGraphClean
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The old graph has the supplied uniqueness property at target 28. -/
def oldUnique : Nat := imp
  (both (member 31 4) (graphFormula 6 4 28).encode) (equal 4 2)

/-- An extended edge is either old or the new (31,32) top edge. -/
def edgeSplit : Nat := imp (graphFormula 9 4 28).encode
  (either (graphFormula 6 4 28).encode (both (equal 4 31) (equal 28 32)))

/-- The old graph edge has its source in the old source domain. -/
def oldSourceGuard : Nat := imp (graphFormula 6 4 28).encode (member 31 4)

/-- An old target cannot be reached by the distinct appended top edge, so
its supplied old preimage remains unique in the extended graph. -/
def old_target_unique_point : KDerivation (imp suffix (imp (member 34 28)
    (imp oldUnique (imp edgeSplit (imp oldSourceGuard
      (imp (graphFormula 9 4 28).encode (equal 4 2))))))) := by
  let F := suffix
  let T := member 34 28
  let U := oldUnique
  let S := edgeSplit
  let D := oldSourceGuard
  let G := (graphFormula 9 4 28).encode
  let O := (graphFormula 6 4 28).encode
  let E := both (equal 4 31) (equal 28 32)
  let Γ := [G,D,S,U,T,F]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .head _ _
  have hc : Context Γ (either O E) := .mp hg hs
  apply Context.disjunctionElim hc
  · have ho : Context (O :: Γ) O := .head _ _
    have hsrc : Context (O :: Γ) (member 31 4) := .mp ho (.under hd _)
    exact .mp (Context.conjunctionIntro hsrc ho) (.under hu _)
  · have he : Context (E :: Γ) E := .head _ _
    have heq : Context (E :: Γ) (equal 28 32) := Context.conjunctionRight he
    have hmem : Context (E :: Γ) (member 34 32) :=
      .mp heq (.mp (.under ht _) (.closed (memberRightEquality 34 28 32)))
    have hnot : Context (E :: Γ) (neg (member 34 32)) :=
      .mp (.under hf _) (.closed result_outside_suffix)
    exact Context.explode (equal 4 2) (.mp hmem hnot)

theorem old_target_unique_point_certificate :
    theoremCode (certificate old_target_unique_point) =
      imp suffix (imp (member 34 28) (imp oldUnique (imp edgeSplit
        (imp oldSourceGuard (imp (graphFormula 9 4 28).encode (equal 4 2)))))) :=
  certificate_correct old_target_unique_point
end PASoundness.PAtoCompactAdditionOldTargetPoint
#print axioms PASoundness.PAtoCompactAdditionOldTargetPoint.old_target_unique_point
#print axioms PASoundness.PAtoCompactAdditionOldTargetPoint.old_target_unique_point_certificate
