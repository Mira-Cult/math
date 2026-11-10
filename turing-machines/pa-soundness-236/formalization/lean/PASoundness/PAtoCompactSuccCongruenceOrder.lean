import PASoundness.PAtoCompactSuccCongruenceEdgeSplit
import PASoundness.PAtoCompactSuccOrderOldOld
import PASoundness.PAtoCompactSuccMixedOrderTransport
import PASoundness.PAtoCompactSuccOrderContextVacuity
import PASoundness.PAtoCompactSuccBijectionPremises

/-! Conditional successor-order preservation for a clean represented graph.
All graph, pair, old-order and domain-transitivity premises remain explicit.
This constructs literal K proof data; no graph collection or unconditional
quotient congruence is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccCongruenceOrder
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.PAtoCompactSuccCongruenceEdgeSplit PASoundness.PAtoCompactSuccOrderOldOld
open PASoundness.PAtoCompactSuccCongruenceOrderAlpha PASoundness.PAtoCompactSuccCleanEndpoint
open PASoundness.PAtoCompactSuccCongruenceMixedOrder PASoundness.PAtoCompactSuccMixedOrder45
open PASoundness.PAtoCompactSuccMixedOrderTransport PASoundness.PAtoCompactSuccOrderPointShape
open PASoundness.PAtoCompactSuccOrderPointLift PASoundness.PAtoCompactSuccOrderContextVacuity
open PASoundness.PAtoCompactSuccBijectionPremises

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The four old/new edge cases imply the exact pointwise order comparison. -/
def point_comparison : Context (guards :: orderContext) comparison := by
  let G23 := (graphFormula 6 2 3).encode
  let G45 := (graphFormula 6 4 5).encode
  let T23 := both (equal 2 0) (equal 3 1)
  let T45 := both (equal 4 0) (equal 5 1)
  let Δ := guards :: orderContext
  have hguard : Context Δ guards := Context.head _ _
  have hpair : Context Δ newPair := .hypothesis (by simp [Δ,orderContext])
  have hgraph : Context Δ newGraph := .hypothesis (by simp [Δ,orderContext])
  have hrest := Context.conjunctionRight (Context.conjunctionRight
    (Context.conjunctionRight (Context.conjunctionRight hguard)))
  have hg23 : Context Δ (graphFormula 9 2 3).encode := Context.conjunctionLeft hrest
  have hg45 : Context Δ (graphFormula 9 4 5).encode := Context.conjunctionRight hrest
  have hsplit23 : Context Δ (either G23 T23) := by
    have h := Context.mp hg23 (.mp hpair (.mp hgraph (.closed edge_split)))
    simpa [G23,T23,conclusion,PAtoCompactZeroSuccessor.namedBoth,
      PAtoCompactZeroSuccessor.namedEither,CompactNamed.Formula.encode,
      CompactProof.both,CompactProof.neg,CompactDerivations.either] using h
  have hsplit45 : Context Δ (either G45 T45) :=
    .mp hg45 (.mp hpair (.mp hgraph (.closed edge_split_45)))
  apply Context.disjunctionElim hsplit23
  · have hsplit45' := Context.under hsplit45 G23
    apply Context.disjunctionElim hsplit45'
    · let Γ := G45 :: G23 :: Δ
      have hO : Context Γ oldOrderFresh.encode := .hypothesis (by simp [Γ,Δ,orderContext])
      have hC : Context Γ cleanGraph := .hypothesis (by simp [Γ,Δ,orderContext])
      have h23 : Context Γ G23 := .hypothesis (by simp [Γ,Δ])
      have h45 : Context Γ G45 := Context.head _ _
      exact .mp h45 (.mp h23 (.mp hC (.mp hO (.closed old_old))))
    · let Γ := T45 :: G23 :: Δ
      have hC : Context Γ cleanGraph := .hypothesis (by simp [Γ,Δ,orderContext])
      have h23 : Context Γ G23 := .hypothesis (by simp [Γ,Δ])
      have hT : Context Γ T45 := Context.head _ _
      have he : Context Γ endpoints := .mp h23 (.mp hC (.closed (clean_endpoints 2 3 (by decide))))
      have hm : Context Γ oldToTop := .mp he (.closed old_to_top)
      exact .mp hm (.mp hT (.closed old_top_transport))
  · have hsplit45' := Context.under hsplit45 T23
    apply Context.disjunctionElim hsplit45'
    · let Γ := G45 :: T23 :: Δ
      have hC : Context Γ cleanGraph := .hypothesis (by simp [Γ,Δ,orderContext])
      have hS : Context Γ sourceTrans := .hypothesis (by simp [Γ,Δ,orderContext])
      have hT : Context Γ targetTrans := .hypothesis (by simp [Γ,Δ,orderContext])
      have h45 : Context Γ G45 := Context.head _ _
      have hTop : Context Γ T23 := .hypothesis (by simp [Γ,Δ])
      have he : Context Γ endpoints45 := .mp h45 (.mp hC (.closed (clean_endpoints 4 5 (by decide))))
      have hm : Context Γ topToOld45 := .mp he (.mp hT (.mp hS (.closed top_to_old45)))
      exact .mp hm (.mp hTop (.closed top_old_transport))
    · let Γ := T45 :: T23 :: Δ
      have h23 : Context Γ T23 := .hypothesis (by simp [Γ,Δ])
      have h45 : Context Γ T45 := Context.head _ _
      exact .mp (.closed top_to_top) (.mp h45 (.mp h23 (.closed top_top_transport)))

/-- Lift the pointwise proof under exactly the six capture-safe assumptions. -/
def order_from_fresh : KDerivation (imp oldOrderFresh.encode (imp cleanGraph
    (imp newGraph (imp newPair (imp sourceTrans (imp targetTrans newOrder.encode)))))) := by
  have hp : Context orderContext pointMatrix.encode := by
    rw [point_encoded_shape]
    exact Context.deduction point_comparison
  have ho : Context orderContext newOrder.encode := context_point_lift orderContext
    (context_vacuity 5 (by decide)) (context_vacuity 3 (by decide))
    (context_vacuity 4 (by decide)) (context_vacuity 2 (by decide)) hp
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact ho

/-- Project the exact bijection-premise conjunction and retain both explicit
transitivity hypotheses to derive the new order clause. -/
def order_closed : KDerivation (imp premisesCode
    (imp sourceTrans (imp targetTrans newOrder.encode))) := by
  let Γ := [targetTrans,sourceTrans,premisesCode]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hp : Context Γ premisesCode := .hypothesis (by simp [Γ])
  have hs : Context Γ sourceTrans := .hypothesis (by simp [Γ])
  have ht : Context Γ targetTrans := Context.head _ _
  have hm : Context Γ oldMatrix := Context.conjunctionLeft hp
  have hc : Context Γ cleanGraph := Context.conjunctionLeft (Context.conjunctionRight hp)
  have hpair : Context Γ newPair := Context.conjunctionLeft
    (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hp))))
  have hgraph : Context Γ newGraph := Context.conjunctionLeft
    (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hp)))))
  have hOld : Context Γ orderFormula.encode := Context.conjunctionRight hm
  have hFresh : Context Γ oldOrderFresh.encode := .mp hOld (.closed order_alpha)
  exact .mp ht (.mp hs (.mp hpair (.mp hgraph (.mp hc (.mp hFresh (.closed order_from_fresh))))))

theorem order_closed_certificate : theoremCode (certificate order_closed) =
    imp premisesCode (imp sourceTrans (imp targetTrans newOrder.encode)) :=
  certificate_correct order_closed

end PASoundness.PAtoCompactSuccCongruenceOrder

#print axioms PASoundness.PAtoCompactSuccCongruenceOrder.order_from_fresh
#print axioms PASoundness.PAtoCompactSuccCongruenceOrder.order_closed
#print axioms PASoundness.PAtoCompactSuccCongruenceOrder.order_closed_certificate
