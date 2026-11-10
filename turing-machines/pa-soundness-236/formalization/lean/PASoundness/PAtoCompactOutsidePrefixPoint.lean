import PASoundness.PAtoCompactTransitiveClosure

/-! Pointwise outside-source successor case for the partial inverse invariant.
Names are literal K variable names; compact negation uses code 1. This only
compares prefix memberships under the displayed assumptions. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactOutsidePrefixPoint
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuccessorInjective
open PASoundness.PAtoCompactTransitiveClosure
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- If old prefix 8 is outside source 0, then for a source element 2,
membership in its successor prefix 10 agrees with membership in 8. -/
def outside_prefix_point : KDerivation
    (imp (successorCode 8 10 15)
      (imp (neg (member 0 8)) (imp (member 0 2)
        (both (imp (member 10 2) (member 8 2))
          (imp (member 8 2) (member 10 2)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let S := successorCode 8 10 15
  let N := neg (member 0 8)
  let X := member 0 2
  let A := member 10 2
  let B := member 8 2
  let Γ := [X,N,S]
  have hx : Context Γ X := Context.head _ _
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hforward : Context Γ (imp A B) := by
    apply Context.deduction
    let Δ := [A,X,N,S]
    have ha : Context Δ A := Context.head _ _
    have hs' : Context Δ S := Context.under hs A
    have hsplit : Context Δ (either (equal 2 8) B) :=
      .mp ha (.mp hs' (.closed (successor_inspect 8 10 15 2 (by decide) (by decide) (by decide))))
    apply Context.disjunctionElim hsplit
    · let Θ := [equal 2 8,A,X,N,S]
      have he : Context Θ (equal 2 8) := Context.head _ _
      have hx' : Context Θ X := Context.under (Context.under hx A) (equal 2 8)
      have hn' : Context Θ N := Context.under (Context.under hn A) (equal 2 8)
      have hm : Context Θ (member 0 8) := .mp he (.mp hx' (.closed (memberRightEquality 0 2 8)))
      exact Context.explode B (.mp hm hn')
    · exact Context.head Δ B
  have hback : Context Γ (imp B A) := by
    apply Context.deduction
    let Δ := [B,X,N,S]
    have hb : Context Δ B := Context.head _ _
    have hs' : Context Δ S := Context.under hs B
    have hd : Context Δ (either (equal 2 8) B) := Context.disjunctionRight hb
    exact .mp hd (.mp hs' (.closed (successor_include 8 10 15 2 (by decide) (by decide) (by decide))))
  exact Context.conjunctionIntro hforward hback

theorem outside_prefix_point_certificate :
    theoremCode (certificate outside_prefix_point) =
      imp (successorCode 8 10 15)
        (imp (neg (member 0 8)) (imp (member 0 2)
          (both (imp (member 10 2) (member 8 2))
            (imp (member 8 2) (member 10 2))))) :=
  certificate_correct outside_prefix_point

end PASoundness.PAtoCompactOutsidePrefixPoint

#print axioms PASoundness.PAtoCompactOutsidePrefixPoint.outside_prefix_point
#print axioms PASoundness.PAtoCompactOutsidePrefixPoint.outside_prefix_point_certificate
