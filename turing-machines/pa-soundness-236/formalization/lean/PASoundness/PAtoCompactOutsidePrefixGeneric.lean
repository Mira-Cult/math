import PASoundness.PAtoCompactTransitiveClosure

/-! Generic literal-K outside-source successor comparison. The theorem uses
only the supplied successor graph, encoded nonmembership and source guard;
it does not construct any composition graph or prove a collection principle.
Compact negation is implication into literal code 1. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactOutsidePrefixGeneric
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuccessorInjective
open PASoundness.PAtoCompactTransitiveClosure
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- If a prefix endpoint is outside a source, its old and successor prefixes
have the same membership at every supplied source member. Only the successor
graph's test label is required to be distinct from its two object names and
the queried name; the objects' interpreted values may coincide. -/
def outside_prefix_point (source old next query test : Nat)
    (hto : test ≠ old) (htn : test ≠ next) (htq : test ≠ query) :
    KDerivation (imp (successorCode old next test)
      (imp (neg (member source old)) (imp (member source query)
        (both (imp (member next query) (member old query))
          (imp (member old query) (member next query)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let S := successorCode old next test
  let N := neg (member source old)
  let X := member source query
  let A := member next query
  let B := member old query
  let Γ := [X,N,S]
  have hx : Context Γ X := Context.head _ _
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hforward : Context Γ (imp A B) := by
    apply Context.deduction
    let Δ := [A,X,N,S]
    have ha : Context Δ A := Context.head _ _
    have hs' : Context Δ S := Context.under hs A
    have hsplit : Context Δ (either (equal query old) B) :=
      .mp ha (.mp hs' (.closed (successor_inspect old next test query hto htn htq)))
    apply Context.disjunctionElim hsplit
    · let Θ := [equal query old,A,X,N,S]
      have he : Context Θ (equal query old) := Context.head _ _
      have hx' : Context Θ X := Context.under (Context.under hx A) (equal query old)
      have hn' : Context Θ N := Context.under (Context.under hn A) (equal query old)
      have hm : Context Θ (member source old) :=
        .mp he (.mp hx' (.closed (memberRightEquality source query old)))
      exact Context.explode B (.mp hm hn')
    · exact Context.head Δ B
  have hback : Context Γ (imp B A) := by
    apply Context.deduction
    let Δ := [B,X,N,S]
    have hb : Context Δ B := Context.head _ _
    have hs' : Context Δ S := Context.under hs B
    have hd : Context Δ (either (equal query old) B) := Context.disjunctionRight hb
    exact .mp hd (.mp hs' (.closed (successor_include old next test query hto htn htq)))
  exact Context.conjunctionIntro hforward hback

theorem outside_prefix_point_certificate (source old next query test : Nat)
    (hto : test ≠ old) (htn : test ≠ next) (htq : test ≠ query) :
    theoremCode (certificate (outside_prefix_point source old next query test hto htn htq)) =
      imp (successorCode old next test)
        (imp (neg (member source old)) (imp (member source query)
          (both (imp (member next query) (member old query))
            (imp (member old query) (member next query))))) :=
  certificate_correct (outside_prefix_point source old next query test hto htn htq)

end PASoundness.PAtoCompactOutsidePrefixGeneric

#print axioms PASoundness.PAtoCompactOutsidePrefixGeneric.outside_prefix_point
#print axioms PASoundness.PAtoCompactOutsidePrefixGeneric.outside_prefix_point_certificate
