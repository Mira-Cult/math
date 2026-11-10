import PASoundness.PAtoCompactProductMatchPartialBase
import PASoundness.PAtoCompactOutsidePrefixGeneric
import PASoundness.PAtoCompactPartialInverseOutsideTransfer
import PASoundness.PAtoCompactFreeVacuity

/-! The outside-source branch of the partial product-match successor step.
The same represented graph remains valid: this does not prove the inside
branch, full strong induction step, or graph collection. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchOutsideStep

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactOutsidePrefixGeneric PASoundness.PAtoCompactPartialInverseOutsideTransfer
open PASoundness.PAtoCompactProductMatchPartialBase

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def oldMatch : Formula := replace 59 74 partialMatch
def oldPoint : Formula := .imp (namedBoth (.member 2 56) (.member 44 57))
  (namedBoth (.imp (graphFormula 58 56 57) (namedBoth (.member 74 56) matchAt))
    (.imp (namedBoth (.member 74 56) matchAt) (graphFormula 58 56 57)))

theorem old_match_shape : oldMatch = .all 56 (.all 57 oldPoint) := by decide

/-- Specialize the old guarded graph invariant at the two displayed endpoint
names without changing their interpreted values. -/
def old_match_instance : KDerivation (imp oldMatch.encode oldPoint.encode) := by
  have h56 := allSpecialize 56 (.all 57 oldPoint) (by decide)
  have h57 := allSpecialize 57 oldPoint (by decide)
  rw [old_match_shape]
  exact compose h56 h57

/-- If old prefix 74 is outside source 2, successor 59 introduces no new
source-relevant edge and the old graph still satisfies the next invariant. -/
def outside_successor : KDerivation
    (imp oldMatch.encode (imp (successorCode 74 59 76)
      (imp (neg (member 2 74)) partialMatch.encode))) := by
  let P := oldMatch.encode
  let S := successorCode 74 59 76
  let N := neg (member 2 74)
  let X := member 2 56
  let Y := member 44 57
  let H := (graphFormula 58 56 57).encode
  let M := member 74 56
  let Q := member 59 56
  let O := matchAt.encode
  let old := imp (both X Y) (both (imp H (both M O)) (imp (both M O) H))
  let new := imp (both X Y) (both (imp H (both Q O)) (imp (both Q O) H))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [N,S,P]
  have hn : Context Γ N := .head _ _
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hold : Context Γ old := by
    have h : Context Γ oldPoint.encode := .mp hp (.closed old_match_instance)
    simpa [oldPoint, old, X, Y, H, M, O, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hrev : Context Γ (imp X (both (imp Q M) (imp M Q))) :=
    .mp hn (.mp hs (.closed (outside_prefix_point 2 74 59 56 76 (by decide) (by decide) (by decide))))
  have hcomp : Context Γ (imp X (both (imp M Q) (imp Q M))) := by
    apply Context.deduction
    let Δ := [X,N,S,P]
    have hx : Context Δ X := .head _ _
    have hr : Context Δ (imp X (both (imp Q M) (imp M Q))) := .under hrev X
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
    · subst q; exact hN
    · by_cases hs' : q = S
      · subst q; exact hS
      · have hp' : q = P := (hq.resolve_left he).resolve_left hs'
        subst q; exact hP
  have hv56 := hv 56 (free_vacuity 56 oldMatch (by decide))
    (successor_vacuity 74 59 76 56 (by decide) (by decide) (by decide))
    (negationVacuity 56 (membershipVacuity 2 74 56 (by decide) (by decide)))
  have hv57 := hv 57 (free_vacuity 57 oldMatch (by decide))
    (successor_vacuity 74 59 76 57 (by decide) (by decide) (by decide))
    (negationVacuity 57 (membershipVacuity 2 74 57 (by decide) (by decide)))
  have h := Context.generalize 56 hv56 (Context.generalize 57 hv57 hpoint)
  simpa [Γ, N, S, P, partialMatch, namedBoth, Formula.not, Formula.encode, both, neg,
    new, X, Y, H, Q, O] using h

theorem old_instance : replace 64 74 predicate = .ex 58 oldMatch := by decide
theorem next_instance : replace 64 59 predicate = .ex 58 partialMatch := by decide

/-- The outside branch keeps exactly the old existential graph witness. -/
def outside_predicate_step : KDerivation
    (imp (successorCode 74 59 76) (imp (neg (member 2 74))
      (imp (replace 64 74 predicate).encode (replace 64 59 predicate).encode))) := by
  let S := successorCode 74 59 76
  let N := neg (member 2 74)
  let P := oldMatch.encode
  let Q := partialMatch.encode
  have hreorder : KDerivation (imp S (imp N (imp P Q))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [P,N,S]
    have hp : Context Γ P := .head _ _
    have hn : Context Γ N := .hypothesis (by simp [Γ])
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    exact .mp hn (.mp hs (.mp hp (.closed outside_successor)))
  rw [old_instance, next_instance]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [existsCode 58 P,N,S]
  have he : Context Γ (existsCode 58 P) := .head _ _
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hS : Context Γ (allCode 58 S) := .mp hs
    (.closed (successor_vacuity 74 59 76 58 (by decide) (by decide) (by decide)))
  have hN : Context Γ (allCode 58 N) := .mp hn
    (.closed (negationVacuity 58 (membershipVacuity 2 74 58 (by decide) (by decide))))
  have hall : Context Γ (allCode 58 (imp P Q)) :=
    Context.allMP hN (Context.allMP hS (.closed (.generalize 58 hreorder)))
  simpa [Formula.encode, P, Q] using exists_map_context hall he

theorem outside_predicate_step_certificate :
    theoremCode (certificate outside_predicate_step) =
      imp (successorCode 74 59 76) (imp (neg (member 2 74))
        (imp (replace 64 74 predicate).encode (replace 64 59 predicate).encode)) := certificate_correct _

end PASoundness.PAtoCompactProductMatchOutsideStep

#print axioms PASoundness.PAtoCompactProductMatchOutsideStep.old_match_instance
#print axioms PASoundness.PAtoCompactProductMatchOutsideStep.outside_successor
#print axioms PASoundness.PAtoCompactProductMatchOutsideStep.outside_predicate_step
#print axioms PASoundness.PAtoCompactProductMatchOutsideStep.outside_predicate_step_certificate
