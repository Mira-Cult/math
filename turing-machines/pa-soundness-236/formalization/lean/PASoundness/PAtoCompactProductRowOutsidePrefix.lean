import PASoundness.PAtoCompactZeroSuccessor
import PASoundness.CompactNamed

/-! One K step for product-row collection: if the newly adjoined prefix point
is outside the row's index set, intersecting the prefix with that set is
unchanged. This pointwise lemma neither constructs a row graph nor proves a
multiplication relation. Compact negation is literal implication to code 1. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductRowOutsidePrefix
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- At the supplied test point, successor extension adds nothing to the
intersection when the old prefix is outside the index set. -/
def outside_intersection_point : KDerivation
    (imp (successorCode 0 1 2) (imp (neg (member 31 0))
      (both (imp (both (member 1 3) (member 31 3)) (both (member 0 3) (member 31 3)))
        (imp (both (member 0 3) (member 31 3)) (both (member 1 3) (member 31 3)))))) := by
  let f := namedSuccessorBody 0 1 2
  have hi := universalInstance 2 3 f (by decide) (by decide) (by decide)
  have hi' : KDerivation (imp (successorCode 0 1 2)
      (both (imp (member 1 3) (either (equal 3 0) (member 0 3)))
        (imp (either (equal 3 0) (member 0 3)) (member 1 3)))) := by
    simpa [f,namedSuccessorBody,namedBoth,namedEither,successorCode,
      Formula.encode,replace,rename,both,neg,either] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let S := successorCode 0 1 2
  let N := neg (member 31 0)
  let Γ := [N,S]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hcases := Context.conjunctionLeft (.mp hs (.closed hi'))
  have hbuild := Context.conjunctionRight (.mp hs (.closed hi'))
  apply Context.conjunctionIntro
  · apply Context.deduction
    let Δ := [both (member 1 3) (member 31 3),N,S]
    have hp : Context Δ (both (member 1 3) (member 31 3)) := .head _ _
    have hy := Context.conjunctionRight hp
    have hc : Context Δ (either (equal 3 0) (member 0 3)) :=
      .mp (Context.conjunctionLeft hp) (.under hcases _)
    apply Context.disjunctionElim hc
    · let Θ := [equal 3 0,both (member 1 3) (member 31 3),N,S]
      have he : Context Θ (equal 3 0) := .head _ _
      have hbad : Context Θ (member 31 0) :=
        .mp he (.mp (.under hy _) (.closed (memberRightEquality 31 3 0)))
      have hn' : Context Θ N := .hypothesis (by simp [Θ])
      exact Context.explode (both (member 0 3) (member 31 3)) (.mp hbad hn')
    · let Θ := [member 0 3,both (member 1 3) (member 31 3),N,S]
      exact Context.conjunctionIntro (.head _ _) (.under hy _)
  · apply Context.deduction
    let Δ := [both (member 0 3) (member 31 3),N,S]
    have hp : Context Δ (both (member 0 3) (member 31 3)) := .head _ _
    have hx := Context.conjunctionLeft hp
    have hy := Context.conjunctionRight hp
    have hs' : Context Δ (member 1 3) :=
      .mp (Context.disjunctionRight hx) (.under hbuild _)
    exact Context.conjunctionIntro hs' hy

theorem outside_intersection_point_certificate :
    theoremCode (certificate outside_intersection_point) =
      imp (successorCode 0 1 2) (imp (neg (member 31 0))
        (both (imp (both (member 1 3) (member 31 3)) (both (member 0 3) (member 31 3)))
          (imp (both (member 0 3) (member 31 3)) (both (member 1 3) (member 31 3))))) :=
  certificate_correct outside_intersection_point
end PASoundness.PAtoCompactProductRowOutsidePrefix
#print axioms PASoundness.PAtoCompactProductRowOutsidePrefix.outside_intersection_point
#print axioms PASoundness.PAtoCompactProductRowOutsidePrefix.outside_intersection_point_certificate
