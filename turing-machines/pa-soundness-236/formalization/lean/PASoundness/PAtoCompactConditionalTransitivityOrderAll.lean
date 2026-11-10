import PASoundness.PAtoCompactConditionalTransitivityOrderComposite
import PASoundness.PAtoCompactConditionalTransitivityOrderTargetSyntax
import PASoundness.PAtoCompactConditionalTransitivityQuantVacuity

/-! Quantified order transfer through an explicitly supplied restricted
composition graph. This proves neither graph existence nor full isomorphism
or quotient transitivity. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityOrderAll
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityPoint
open PASoundness.PAtoCompactConditionalTransitivityElimSecond
open PASoundness.PAtoCompactConditionalTransitivityOrderSecond
open PASoundness.PAtoCompactConditionalTransitivityOrderComposite
open PASoundness.PAtoCompactConditionalTransitivityOrderTargetSyntax
open PASoundness.PAtoCompactConditionalTransitivityQuantVacuity
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Both source order clauses and the supplied restricted composition imply
the exact renamed target order clause. Four target-domain guards and both
composite edges remain under the target's literal quantified implication. -/
def composite_order : KDerivation
    (imp orderFormula.encode (imp secondOrder.encode
      (imp composition.encode targetOrder.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := assumptions
  have ho : Context Γ orderFormula.encode := .hypothesis (by simp [Γ, assumptions])
  have hs : Context Γ secondOrder.encode := .hypothesis (by simp [Γ, assumptions])
  have hc : Context Γ composition.encode := Context.head _ _
  have hp : Context Γ targetPoint.encode := by
    change Context Γ (imp targetGuard conclusion.encode)
    apply Context.deduction
    let Δ := targetGuard :: Γ
    have hg : Context Δ targetGuard := Context.head _ _
    have ha : Context Δ (member 0 2) := Context.conjunctionLeft hg
    have ht := Context.conjunctionRight hg
    have ha' : Context Δ (member 0 4) := Context.conjunctionLeft ht
    have ht := Context.conjunctionRight ht
    have hb : Context Δ (member 8 3) := Context.conjunctionLeft ht
    have ht := Context.conjunctionRight ht
    have hb' : Context Δ (member 8 5) := Context.conjunctionLeft ht
    have ht := Context.conjunctionRight ht
    have he : Context Δ edge.encode := Context.conjunctionLeft ht
    have he' : Context Δ secondEdge.encode := Context.conjunctionRight ht
    have hP : Context Δ premises.encode :=
      Context.conjunctionIntro (.under ho targetGuard)
        (Context.conjunctionIntro (.under hs targetGuard)
          (Context.conjunctionIntro (.under hc targetGuard)
            (Context.conjunctionIntro ha (Context.conjunctionIntro ha'
              (Context.conjunctionIntro hb (Context.conjunctionIntro hb'
                (Context.conjunctionIntro he he')))))))
    exact .mp hP (.closed guarded_composite_order)
  have hall := Context.generalize 2 context_vacuity2
    (Context.generalize 4 context_vacuity4
      (Context.generalize 3 context_vacuity3 (Context.generalize 5 context_vacuity5 hp)))
  simpa only [target_order_syntax, Formula.encode, assumptions] using hall

theorem composite_order_certificate :
    theoremCode (certificate composite_order) =
      imp orderFormula.encode (imp secondOrder.encode
        (imp composition.encode targetOrder.encode)) :=
  certificate_correct composite_order

end PASoundness.PAtoCompactConditionalTransitivityOrderAll

#print axioms PASoundness.PAtoCompactConditionalTransitivityOrderAll.composite_order
#print axioms PASoundness.PAtoCompactConditionalTransitivityOrderAll.composite_order_certificate
