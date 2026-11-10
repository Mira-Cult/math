import PASoundness.PAtoCompactTransitiveClosure
import PASoundness.PAtoCompactZeroSuccessor

/-! Fixed-label K lemmas for preserving an addition cut through a raw
successor. The explicit transitivity, cut alternative, and successor graph
are premises. No addition axiom, quotient property, or arithmetic totality
is asserted. Negation is literal implication to compact code 1. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorCut
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveClosure
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- A cut equal to a transitive result, or belonging to it, cannot contain
the result unless literal code 1 holds. -/
def result_outside_cut : KDerivation
    (imp (transitiveCode 32 42 43)
      (imp (either (equal 33 32) (member 32 33)) (neg (member 33 32)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 33 32, either (equal 33 32) (member 32 33), transitiveCode 32 42 43]
  have hm : Context Γ (member 33 32) := .head _ _
  have ha : Context Γ (either (equal 33 32) (member 32 33)) := .hypothesis (by simp [Γ])
  have ht : Context Γ (transitiveCode 32 42 43) := .hypothesis (by simp [Γ])
  apply Context.disjunctionElim ha
  · have he : Context (equal 33 32 :: Γ) (equal 33 32) := .head _ _
    have hself : Context (equal 33 32 :: Γ) (member 32 32) :=
      .mp (.under hm _) (.mp he (.closed (memberLeftEquality 33 32 32)))
    exact .mp hself (.closed (self_membership_implies_code_one 32))
  · have hc : Context (member 32 33 :: Γ) (member 32 33) := .head _ _
    have hself : Context (member 32 33 :: Γ) (member 32 32) :=
      .mp (.under hm _) (.mp hc (.mp (.under ht _) (.closed
        (transitive_instance 32 33 42 43 (by decide) (by decide) (by decide)
          (by decide) (by decide)))))
    exact .mp hself (.closed (self_membership_implies_code_one 32))

/-- The old cut belongs to the successor of the result. -/
def cut_in_result_successor : KDerivation
    (imp (successorCode 32 38 39)
      (imp (either (equal 33 32) (member 32 33)) (member 38 33))) := by
  let body := namedSuccessorBody 32 38 39
  have hi := universalInstance 39 33 body (by decide)
    (by simp [body,namedSuccessorBody,namedBoth,namedEither,Formula.binders])
    (by simp [body,namedSuccessorBody,namedBoth,namedEither,Formula.binders])
  have hi' : KDerivation (imp (successorCode 32 38 39)
      (both (imp (member 38 33) (either (equal 33 32) (member 32 33)))
        (imp (either (equal 33 32) (member 32 33)) (member 38 33)))) := by
    simpa [body,namedSuccessorBody,namedBoth,namedEither,successorCode,
      Formula.encode,replace,rename,both,neg,either] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [either (equal 33 32) (member 32 33),successorCode 32 38 39]
  have ha : Context Γ (either (equal 33 32) (member 32 33)) := .head _ _
  have hs : Context Γ (successorCode 32 38 39) := .hypothesis (by simp [Γ])
  exact .mp ha (Context.conjunctionRight (.mp hs (.closed hi')))

theorem result_outside_cut_certificate : theoremCode (certificate result_outside_cut) =
    imp (transitiveCode 32 42 43)
      (imp (either (equal 33 32) (member 32 33)) (neg (member 33 32))) :=
  certificate_correct result_outside_cut

theorem cut_in_result_successor_certificate : theoremCode (certificate cut_in_result_successor) =
    imp (successorCode 32 38 39)
      (imp (either (equal 33 32) (member 32 33)) (member 38 33)) :=
  certificate_correct cut_in_result_successor
end PASoundness.PAtoCompactAdditionSuccessorCut

#print axioms PASoundness.PAtoCompactAdditionSuccessorCut.result_outside_cut
#print axioms PASoundness.PAtoCompactAdditionSuccessorCut.result_outside_cut_certificate
#print axioms PASoundness.PAtoCompactAdditionSuccessorCut.cut_in_result_successor
#print axioms PASoundness.PAtoCompactAdditionSuccessorCut.cut_in_result_successor_certificate
