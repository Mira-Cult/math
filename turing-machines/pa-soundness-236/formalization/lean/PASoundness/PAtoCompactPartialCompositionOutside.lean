import PASoundness.PAtoCompactPartialCompositionInstantiate
import PASoundness.PAtoCompactOutsidePrefixGeneric
import PASoundness.PAtoCompactPartialInverseOutsideTransfer

/-! Outside-source successor branch for the partial-composition invariant.
When old prefix 10 is outside source 0, its successor 13 introduces no new
source-relevant pair and the supplied graph 9 remains valid. This derives no
composition graph existence or quotient transitivity. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionOutside
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactPartialCompositionBase
open PASoundness.PAtoCompactPartialCompositionInstantiate PASoundness.PAtoCompactOutsidePrefixGeneric
open PASoundness.PAtoCompactPartialInverseOutsideTransfer
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The unchanged graph invariant at the successor prefix. -/
def nextPartialComposition : Formula := replace 10 13 partialComposition

/-- From a supplied successor graph and nonmembership in the source, K carries
all guarded composition equivalences to the new prefix with the same graph. -/
def outside_successor : KDerivation
    (imp partialComposition.encode (imp (successorCode 10 13 15)
      (imp (neg (member 0 10)) nextPartialComposition.encode))) := by
  let P := partialComposition.encode
  let S := successorCode 10 13 15
  let N := neg (member 0 10)
  let X := member 0 2
  let Y := member 8 3
  let H := (graphFormula 9 2 3).encode
  let M := member 10 2
  let Q := member 13 2
  let O := existsCode 4 (both (member 1 4)
    (both (graphFormula 6 2 4).encode (graphFormula 7 4 3).encode))
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
    have h : Context Γ pointFormula.encode := .mp hp (.closed partial_composition_instance)
    simpa only [P, old, X, Y, H, M, O, point_formula_code] using h
  have hrev : Context Γ (imp X (both (imp Q M) (imp M Q))) :=
    .mp hn (.mp hs (.closed (outside_prefix_point 0 10 13 2 15 (by decide) (by decide) (by decide))))
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
  have hv2 := hv 2 partial_composition_vacuity_2
    (successor_vacuity 10 13 15 2 (by decide) (by decide) (by decide))
    (negationVacuity 2 (membershipVacuity 0 10 2 (by decide) (by decide)))
  have hv3 := hv 3 partial_composition_vacuity_3
    (successor_vacuity 10 13 15 3 (by decide) (by decide) (by decide))
    (negationVacuity 3 (membershipVacuity 0 10 3 (by decide) (by decide)))
  exact Context.generalize 2 hv2 (Context.generalize 3 hv3 hpoint)

theorem outside_successor_certificate :
    theoremCode (certificate outside_successor) =
      imp partialComposition.encode (imp (successorCode 10 13 15)
        (imp (neg (member 0 10)) nextPartialComposition.encode)) :=
  certificate_correct outside_successor

end PASoundness.PAtoCompactPartialCompositionOutside

#print axioms PASoundness.PAtoCompactPartialCompositionOutside.outside_successor
#print axioms PASoundness.PAtoCompactPartialCompositionOutside.outside_successor_certificate
