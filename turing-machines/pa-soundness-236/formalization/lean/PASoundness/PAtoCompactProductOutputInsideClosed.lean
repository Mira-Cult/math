import PASoundness.PAtoCompactProductOutputInsideAdjoinClosed
import PASoundness.PAtoCompactProductOutputInsideExtension

/-! The inside-source successor step for the transported product-graph
partial invariant. The supplied source product matrix and output bijection
remain literal object hypotheses; no candidate or global induction follows
without the separate candidate-induction assembly. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputInsideClosed

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactProductOutputPartialBase PASoundness.PAtoCompactProductOutputOutsideStep
open PASoundness.PAtoCompactProductOutputCollectionInsideConditional
open PASoundness.PAtoCompactProductOutputInsideSelected PASoundness.PAtoCompactProductOutputInsideExtension
open PASoundness.PAtoCompactProductOutputInsideAdjoinClosed

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def insideGuard : Formula := namedBoth assumptions
  (namedBoth (namedSuccessor 74 59 76) (.member 0 74))

/-- The selected source coordinates, image and graph-extension witnesses all
belong to the same old graph. -/
noncomputable def selected_extension_point : KDerivation (imp retained.encode
    (imp selectedWithExtension.encode result.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [selectedWithExtension.encode,retained.encode]
  have hs : Context Γ selectedWithExtension.encode := .head _ _
  have hr : Context Γ retained.encode := .hypothesis (by simp [Γ])
  have hs' : Context Γ (both relocatedBody.encode PAtoCompactProductOutputTripleExtension.newStatement.encode) := by
    simpa [selectedWithExtension, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hs
  exact .mp (Context.conjunctionRight hs') (.mp (Context.conjunctionLeft hs') (.mp hr (.closed selected_adjoin_closed)))

noncomputable def fixed_old_graph : KDerivation (imp insideGuard.encode (imp oldInvariant.encode result.encode)) := by
  have h33 := guarded_exists_left 33 retained.encode selectedWithExtension.encode result.encode
    (free_vacuity 33 retained (by decide)) (free_vacuity 33 result (by decide)) selected_extension_point
  have h31 := guarded_exists_left 31 retained.encode (existsCode 33 selectedWithExtension.encode) result.encode
    (free_vacuity 31 retained (by decide)) (free_vacuity 31 result (by decide)) h33
  have h30 := guarded_exists_left 30 retained.encode (existsCode 31 (existsCode 33 selectedWithExtension.encode)) result.encode
    (free_vacuity 30 retained (by decide)) (free_vacuity 30 result (by decide)) h31
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldInvariant.encode,insideGuard.encode]
  have ho : Context Γ oldInvariant.encode := .head _ _
  have hg : Context Γ insideGuard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both assumptions.encode (both (successorCode 74 59 76) (member 0 74))) := by
    simpa [insideGuard, namedSuccessor, namedSuccessorBody, successorCode, namedBoth, namedEither,
      CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, either] using hg
  have hr : Context Γ retained.encode := by
    simpa [retained, namedSuccessor, namedSuccessorBody, successorCode, namedBoth, namedEither,
      CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, either] using
      Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight hg')) ho
  have hs := Context.mp (Context.conjunctionRight (Context.conjunctionRight hg'))
    (Context.mp (Context.conjunctionLeft hg') (.closed inside_selected_extension))
  exact .mp hs (.mp hr (.closed h30))

/-- Construct the inside-source successor step without an extra proof-data
premise. Assumptions, successor, source membership and old predicate remain
literal antecedents. -/
noncomputable def inside_step : InsideStep := by
  have helim := guarded_exists_left 58 insideGuard.encode oldInvariant.encode result.encode
    (free_vacuity 58 insideGuard (by decide)) (free_vacuity 58 result (by decide)) fixed_old_graph
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(replace 64 74 predicate).encode,member 0 74,successorCode 74 59 76,assumptions.encode]
  have hp : Context Γ (replace 64 74 predicate).encode := .head _ _
  have hm : Context Γ (member 0 74) := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode 74 59 76) := .hypothesis (by simp [Γ])
  have ha : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ insideGuard.encode := by
    simpa [insideGuard, namedSuccessor, namedSuccessorBody, successorCode, namedBoth, namedEither,
      CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, either] using
      Context.conjunctionIntro ha (Context.conjunctionIntro hs hm)
  have hp' : Context Γ (existsCode 58 oldInvariant.encode) := by
    simpa [old_instance_shape, CompactNamed.Formula.encode] using hp
  have hq := Context.mp hp' (Context.mp hg (.closed helim))
  simpa [result, next_instance_shape, CompactNamed.Formula.encode] using hq

theorem inside_step_certificate : theoremCode (certificate inside_step) =
    imp assumptions.encode (imp (successorCode 74 59 76) (imp (member 0 74)
      (imp (replace 64 74 predicate).encode (replace 64 59 predicate).encode))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputInsideClosed

#print axioms PASoundness.PAtoCompactProductOutputInsideClosed.selected_extension_point
#print axioms PASoundness.PAtoCompactProductOutputInsideClosed.fixed_old_graph
#print axioms PASoundness.PAtoCompactProductOutputInsideClosed.inside_step
#print axioms PASoundness.PAtoCompactProductOutputInsideClosed.inside_step_certificate
