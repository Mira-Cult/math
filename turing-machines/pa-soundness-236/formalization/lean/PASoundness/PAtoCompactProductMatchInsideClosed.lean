import PASoundness.PAtoCompactProductMatchAdjoinInvariant
import PASoundness.PAtoCompactSuccGraphOutputLift

/-! Eliminate the selected target and old graph witnesses from the
inside-source product-match extension. The four supplied product and
factor-bijection matrices remain literal object-level hypotheses. This does
not by itself establish a full product isomorphism or arithmetic congruence. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchInsideClosed

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactProductMatchPartialBase PASoundness.PAtoCompactProductMatchOutsideStep
open PASoundness.PAtoCompactProductMatchInsideImage PASoundness.PAtoCompactProductMatchInsideAdjoinConditional
open PASoundness.PAtoCompactProductMatchAdjoinInvariant PASoundness.PAtoCompactProductMatchCollectionInsideConditional

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def innerGuard : Formula := namedBoth assumptions (namedBoth (namedSuccessor 74 59 76)
  (namedBoth (.member 2 74) oldMatch))
def outerGuard : Formula := namedBoth assumptions
  (namedBoth (namedSuccessor 74 59 76) (.member 2 74))

/-- Retain the selected path and the old graph while constructing the
point-adjoined graph satisfying the next invariant. -/
def selected_extension : KDerivation
    (imp selectedPath.encode (imp (successorCode 74 59 76)
      (imp oldMatch.encode (existsCode 58 partialMatch.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldMatch.encode,successorCode 74 59 76,selectedPath.encode]
  have ho : Context Γ oldMatch.encode := .head _ _
  have hs : Context Γ (successorCode 74 59 76) := .hypothesis (by simp [Γ])
  have hp : Context Γ selectedPath.encode := .hypothesis (by simp [Γ])
  have hr : Context Γ retained.encode := by
    have h := Context.conjunctionIntro hp (Context.conjunctionIntro hs ho)
    simpa [retained, namedSuccessor, successorCode, namedSuccessorBody,
      namedBoth, namedEither, Formula.not, Formula.encode, both, neg, either] using h
  exact .mp hr (.closed (new_graph_of_adjoin adjoin_invariant))

/-- Eliminate the chosen target image, keeping the supplied old graph. -/
def inside_with_old_graph : KDerivation (imp assumptions.encode
    (imp (successorCode 74 59 76) (imp (member 2 74)
      (imp oldMatch.encode (existsCode 58 partialMatch.encode))))) := by
  let Q : Formula := .ex 58 partialMatch
  have hpoint : KDerivation (imp innerGuard.encode (imp selectedPath.encode Q.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [selectedPath.encode,innerGuard.encode]
    have hp : Context Γ selectedPath.encode := .head _ _
    have hg : Context Γ innerGuard.encode := .hypothesis (by simp [Γ])
    have hg' : Context Γ (both assumptions.encode (both (successorCode 74 59 76)
        (both (member 2 74) oldMatch.encode))) := by
      simpa [innerGuard, namedSuccessor, successorCode, namedSuccessorBody,
        namedBoth, namedEither, Formula.not, Formula.encode, both, neg, either] using hg
    have hs := Context.conjunctionLeft (Context.conjunctionRight hg')
    have ho := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg'))
    simpa [Q, Formula.encode] using Context.mp ho (Context.mp hs (Context.mp hp (.closed selected_extension)))
  have helim := guarded_exists_left 35 innerGuard.encode selectedPath.encode Q.encode
    (innerGuard.vacuity 35 (by decide)) (Q.vacuity 35 (by decide)) hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldMatch.encode,member 2 74,successorCode 74 59 76,assumptions.encode]
  have ho : Context Γ oldMatch.encode := .head _ _
  have hx : Context Γ (member 2 74) := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode 74 59 76) := .hypothesis (by simp [Γ])
  have hh : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ innerGuard.encode := by
    have h := Context.conjunctionIntro hh (Context.conjunctionIntro hs (Context.conjunctionIntro hx ho))
    simpa [innerGuard, namedSuccessor, successorCode, namedSuccessorBody,
      namedBoth, namedEither, Formula.not, Formula.encode, both, neg, either] using h
  have he : Context Γ (existsCode 35 selectedPath.encode) := .mp hx (.mp hh (.closed inside_image_exists))
  simpa [Q, Formula.encode] using Context.mp he (Context.mp hg (.closed helim))

/-- The full inside branch eliminates the old graph witness as well. -/
def inside_step : InsideStep := by
  let Q : Formula := .ex 58 partialMatch
  have hpoint : KDerivation (imp outerGuard.encode (imp oldMatch.encode Q.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [oldMatch.encode,outerGuard.encode]
    have ho : Context Γ oldMatch.encode := .head _ _
    have hg : Context Γ outerGuard.encode := .hypothesis (by simp [Γ])
    have hg' : Context Γ (both assumptions.encode
        (both (successorCode 74 59 76) (member 2 74))) := by
      simpa [outerGuard, namedSuccessor, successorCode, namedSuccessorBody,
        namedBoth, namedEither, Formula.not, Formula.encode, both, neg, either] using hg
    have hh := Context.conjunctionLeft hg'
    have hs := Context.conjunctionLeft (Context.conjunctionRight hg')
    have hx := Context.conjunctionRight (Context.conjunctionRight hg')
    simpa [Q, Formula.encode] using Context.mp ho
      (Context.mp hx (Context.mp hs (Context.mp hh (.closed inside_with_old_graph))))
  have hv : KDerivation (imp Q.encode (allCode 58 Q.encode)) := free_vacuity 58 Q (by decide)
  have helim := guarded_exists_left 58 outerGuard.encode oldMatch.encode Q.encode
    (outerGuard.vacuity 58 (by decide)) hv hpoint
  change KDerivation (imp assumptions.encode (imp (successorCode 74 59 76)
    (imp (member 2 74) (imp (replace 64 74 predicate).encode (replace 64 59 predicate).encode))))
  rw [old_instance, next_instance]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [existsCode 58 oldMatch.encode,member 2 74,successorCode 74 59 76,assumptions.encode]
  have he : Context Γ (existsCode 58 oldMatch.encode) := .head _ _
  have hx : Context Γ (member 2 74) := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode 74 59 76) := .hypothesis (by simp [Γ])
  have hh : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ outerGuard.encode := by
    have h := Context.conjunctionIntro hh (Context.conjunctionIntro hs hx)
    simpa [outerGuard, namedSuccessor, successorCode, namedSuccessorBody,
      namedBoth, namedEither, Formula.not, Formula.encode, both, neg, either] using h
  simpa [Q, Formula.encode] using Context.mp he (Context.mp hg (.closed helim))

theorem inside_step_certificate : theoremCode (certificate inside_step) =
    imp assumptions.encode (imp (successorCode 74 59 76) (imp (member 2 74)
      (imp (replace 64 74 predicate).encode (replace 64 59 predicate).encode))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchInsideClosed

#print axioms PASoundness.PAtoCompactProductMatchInsideClosed.selected_extension
#print axioms PASoundness.PAtoCompactProductMatchInsideClosed.inside_with_old_graph
#print axioms PASoundness.PAtoCompactProductMatchInsideClosed.inside_step
#print axioms PASoundness.PAtoCompactProductMatchInsideClosed.inside_step_certificate
