import PASoundness.PAtoCompactPartialInverseOutsideTransfer
import PASoundness.PAtoCompactPartialInverseInstantiate
import PASoundness.PAtoCompactOutsidePrefixPoint

/-! The outside-source branch of the partial-inverse successor step. When
prefix 8 is outside source 0, successor prefix 10 changes no source-relevant
edge, so the same graph 7 still satisfies the literal invariant. The stated
successor and nonmembership hypotheses are not constructed here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseOutside
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactPartialInverseBase
open PASoundness.PAtoCompactPartialInverseInstantiate PASoundness.PAtoCompactOutsidePrefixPoint
open PASoundness.PAtoCompactPartialInverseOutsideTransfer
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The invariant with the prefix value moved capture-safely from name 8 to 10. -/
def nextPartialInverse : Formula := replace 8 10 partialInverse

/-- Outside-source successor case: the existing partial-inverse graph remains
valid for the successor prefix. The name 15 tests the supplied successor graph. -/
def outside_successor : KDerivation
    (imp partialInverse.encode (imp (successorCode 8 10 15)
      (imp (neg (member 0 8)) nextPartialInverse.encode))) := by
  let P := partialInverse.encode
  let S := successorCode 8 10 15
  let N := neg (member 0 8)
  let X := member 0 2
  let Y := member 1 3
  let H := (graphFormula 7 3 2).encode
  let M := member 8 2
  let Q := member 10 2
  let O := (graphFormula 6 2 3).encode
  let old := imp (both X Y) (both (imp H (both M O)) (imp (both M O) H))
  let new := imp (both X Y) (both (imp H (both Q O)) (imp (both Q O) H))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [N,S,P]
  have hn : Context Γ N := Context.head _ _
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hold : Context Γ old := by
    have h : Context Γ pointFormula.encode := .mp hp (.closed partial_inverse_instance)
    simpa only [P, old, X, Y, H, M, O, point_formula_code] using h
  have hrev : Context Γ (imp X (both (imp Q M) (imp M Q))) :=
    .mp hn (.mp hs (.closed outside_prefix_point))
  have hcomp : Context Γ (imp X (both (imp M Q) (imp Q M))) := by
    apply Context.deduction
    let Δ := [X,N,S,P]
    have hx : Context Δ X := Context.head _ _
    have hr : Context Δ (imp X (both (imp Q M) (imp M Q))) := Context.under hrev X
    have hboth : Context Δ (both (imp Q M) (imp M Q)) := .mp hx hr
    exact Context.conjunctionIntro (Context.conjunctionRight hboth) (Context.conjunctionLeft hboth)
  have hpoint : Context Γ new := .mp hold (.mp hcomp (.closed (transfer X Y H M Q O)))
  have hv (v : Nat) (hP : KDerivation (imp P (allCode v P)))
      (hS : KDerivation (imp S (allCode v S)))
      (hN : KDerivation (imp N (allCode v N))) :
      ∀ q, q ∈ Γ → KDerivation (imp q (allCode v q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = N
    · subst q
      exact hN
    · by_cases hs' : q = S
      · subst q
        exact hS
      · have hp' : q = P := (hq.resolve_left he).resolve_left hs'
        subst q
        exact hP
  have hv2 := hv 2 partial_inverse_vacuity_2
    (successor_vacuity 8 10 15 2 (by decide) (by decide) (by decide))
    (negationVacuity 2 (membershipVacuity 0 8 2 (by decide) (by decide)))
  have hv3 := hv 3 partial_inverse_vacuity_3
    (successor_vacuity 8 10 15 3 (by decide) (by decide) (by decide))
    (negationVacuity 3 (membershipVacuity 0 8 3 (by decide) (by decide)))
  exact Context.generalize 2 hv2 (Context.generalize 3 hv3 hpoint)

theorem outside_successor_certificate :
    theoremCode (certificate outside_successor) =
      imp partialInverse.encode (imp (successorCode 8 10 15)
        (imp (neg (member 0 8)) nextPartialInverse.encode)) :=
  certificate_correct outside_successor

end PASoundness.PAtoCompactPartialInverseOutside

#print axioms PASoundness.PAtoCompactPartialInverseOutside.outside_successor
#print axioms PASoundness.PAtoCompactPartialInverseOutside.outside_successor_certificate
