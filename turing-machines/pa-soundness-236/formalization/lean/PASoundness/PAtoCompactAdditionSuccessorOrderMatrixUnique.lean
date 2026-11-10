import PASoundness.PAtoCompactAdditionSuccessorOrderAssemble
import PASoundness.PAtoCompactAdditionSuccessorOldOrderVacuity
import PASoundness.PAtoCompactSuccOrderPointLift

/-! Quantification of the unequal-top addition-successor order comparison.
The supplied source and whole-result transitivity assumptions remain explicit;
no transitivity of the relative suffix is assumed. This constructs finite K
proof data under the displayed old-order, graph, pair, and suffix assumptions;
it does not construct the full isomorphism or prove arithmetic totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorOrderMatrixUnique
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.PAtoCompactSuccOrderPointShape PASoundness.PAtoCompactSuccOrderPointLift
open PASoundness.PAtoCompactAdditionSuccessorOldOrderVacuity
open PASoundness.PAtoCompactAdditionSuccessorOrderAssemble
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactFilterInstantiation
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private abbrev O := PASoundness.PAtoCompactAdditionSuccessorOldOld.oldOrder.encode
private abbrev C := PASoundness.PAtoCompactAdditionSuccessorGraphClean.oldClean.encode
private abbrev F := PASoundness.PAtoCompactAdditionSuccessorGraphClean.suffix
private abbrev S := PASoundness.PAtoCompactAdditionSuccessorGraphMixed.sourceTrans
private abbrev T := PASoundness.PAtoCompactAdditionSuccessorGraphMixed.targetTrans
private abbrev P := (pairFormula 11 31 32).encode
private abbrev A := adjoinCode 6 11 9 16

/-- The exact seven fixed assumptions in reverse deduction order. -/
def orderContext : List Nat := [T,S,F,P,A,C,O]

private def suffixFormula : Formula := .all 35
  (namedFilterBody 32 34 35 (Formula.member 33 35).not)
private def transFormula (a : Nat) : Formula := .all 37 (.all 38
  (.imp (.member a 37) (.imp (.member 37 38) (.member a 38))))
private theorem suffix_absent : ∀ x ∈ [2,4,3,5], x ∉ suffixFormula.names := by decide
private theorem source_absent : ∀ x ∈ [2,4,3,5], x ∉ (transFormula 31).names := by decide
private theorem target_absent : ∀ x ∈ [2,4,3,5], x ∉ (transFormula 32).names := by decide
private theorem clean_absent : ∀ x ∈ [2,4,3,5],
    x ∉ PASoundness.PAtoCompactAdditionSuccessorGraphClean.oldClean.names := by decide
private theorem graph_absent : ∀ x ∈ [2,4,3,5], x ∉ (namedAdjoin 6 11 9 16).names := by decide
private theorem pair_absent : ∀ x ∈ [2,4,3,5], x ∉ (pairFormula 11 31 32).names := by decide

/-- Capture-safe K vacuity for each quantified point label. The old-order
case uses proved alpha freshening since its bound labels include 2--5. -/
def context_vacuity (x : Nat) (hx : x ∈ [2,4,3,5]) :
    ∀ h, h ∈ orderContext → KDerivation (imp h (allCode x h)) := by
  intro h hh
  simp only [orderContext,List.mem_cons,List.not_mem_nil,or_false] at hh
  by_cases ht : h = T
  · subst h
    have hv := (transFormula 32).vacuity x (target_absent x hx)
    simpa [transFormula, PASoundness.PAtoCompactAdditionSuccessorGraphMixed.targetTrans,
      transitiveCode, Formula.encode] using hv
  by_cases hs : h = S
  · subst h
    have hv := (transFormula 31).vacuity x (source_absent x hx)
    simpa [transFormula, PASoundness.PAtoCompactAdditionSuccessorGraphMixed.sourceTrans,
      transitiveCode, Formula.encode] using hv
  by_cases hf : h = F
  · subst h
    have hv := suffixFormula.vacuity x (suffix_absent x hx)
    simpa [suffixFormula, PASoundness.PAtoCompactAdditionSuccessorGraphClean.suffix,
      namedFilterBody, filterGraph, filterPredicate, namedBoth, Formula.not, Formula.encode,
      CompactProof.both, CompactProof.neg] using hv
  by_cases hp : h = P
  · subst h
    exact (pairFormula 11 31 32).vacuity x (pair_absent x hx)
  by_cases ha : h = A
  · subst h
    have hv := (namedAdjoin 6 11 9 16).vacuity x (graph_absent x hx)
    simpa [namedAdjoin, adjoinCode, namedBoth, namedEither, Formula.encode,
      CompactProof.both, CompactProof.neg, CompactDerivations.either] using hv
  by_cases hc : h = C
  · subst h
    exact PASoundness.PAtoCompactAdditionSuccessorGraphClean.oldClean.vacuity x (clean_absent x hx)
  have ho : h = O := by simpa [ht,hs,hf,hp,ha,hc] using hh
  subst h
  by_cases h2 : x = 2
  · subst x; exact old_order_vacuity2
  by_cases h4 : x = 4
  · subst x; exact old_order_vacuity4
  by_cases h3 : x = 3
  · subst x; exact old_order_vacuity3
  have h5 : x = 5 := by simpa [h2,h4,h3] using hx
  subst x
  exact old_order_vacuity5

/-- The entire order matrix for the extended graph follows from its old
order, cleanliness, pair and adjunction graphs, suffix filter and transitivity
of the old source and whole old result. -/
def order_matrix : KDerivation (imp O (imp C (imp A (imp P (imp F
    (imp S (imp T newOrder.encode))))))) := by
  have hp : Context orderContext pointMatrix.encode := by
    rw [point_encoded_shape]
    apply Context.deduction
    let Γ := guards :: orderContext
    have hg : Context Γ guards := .head _ _
    have rest := Context.conjunctionRight (Context.conjunctionRight
      (Context.conjunctionRight (Context.conjunctionRight hg)))
    have h23 : Context Γ (graphFormula 9 2 3).encode := Context.conjunctionLeft rest
    have h45 : Context Γ (graphFormula 9 4 5).encode := Context.conjunctionRight rest
    have ho : Context Γ O := .hypothesis (by simp [Γ,orderContext])
    have hc : Context Γ C := .hypothesis (by simp [Γ,orderContext])
    have ha : Context Γ A := .hypothesis (by simp [Γ,orderContext])
    have hpair : Context Γ P := .hypothesis (by simp [Γ,orderContext])
    have hf : Context Γ F := .hypothesis (by simp [Γ,orderContext])
    have hs : Context Γ S := .hypothesis (by simp [Γ,orderContext])
    have ht : Context Γ T := .hypothesis (by simp [Γ,orderContext])
    exact .mp h45 (.mp h23 (.mp ht (.mp hs (.mp hf (.mp hpair (.mp ha
      (.mp hc (.mp ho (.closed point_comparison_closed)))))))))
  have hm : Context orderContext newOrder.encode := context_point_lift orderContext
    (context_vacuity 5 (by decide)) (context_vacuity 3 (by decide))
    (context_vacuity 4 (by decide)) (context_vacuity 2 (by decide)) hp
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hm

theorem order_matrix_certificate : theoremCode (certificate order_matrix) =
    imp O (imp C (imp A (imp P (imp F (imp S (imp T newOrder.encode)))))) :=
  certificate_correct order_matrix
end PASoundness.PAtoCompactAdditionSuccessorOrderMatrixUnique
#print axioms PASoundness.PAtoCompactAdditionSuccessorOrderMatrixUnique.context_vacuity
#print axioms PASoundness.PAtoCompactAdditionSuccessorOrderMatrixUnique.order_matrix
#print axioms PASoundness.PAtoCompactAdditionSuccessorOrderMatrixUnique.order_matrix_certificate
