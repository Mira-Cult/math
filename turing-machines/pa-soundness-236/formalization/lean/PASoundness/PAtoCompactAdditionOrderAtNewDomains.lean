import PASoundness.PAtoCompactAdditionSuccessorOrderMatrixUnique

/-! Capture-safe specialization of the already proved addition-successor
order matrix to source 38 and suffix 40. This retains every original K
premise, assumes no suffix transitivity, and proves no bijection or addition
totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionOrderAtNewDomains
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactAdditionSuccessorOrderMatrixUnique
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private abbrev O := PASoundness.PAtoCompactAdditionSuccessorOldOld.oldOrder.encode
private abbrev C := PASoundness.PAtoCompactAdditionSuccessorGraphClean.oldClean.encode
private abbrev F := PASoundness.PAtoCompactAdditionSuccessorGraphClean.suffix
private abbrev S := PASoundness.PAtoCompactAdditionSuccessorGraphMixed.sourceTrans
private abbrev T := PASoundness.PAtoCompactAdditionSuccessorGraphMixed.targetTrans
private abbrev P := (pairFormula 11 31 32).encode
private abbrev A := adjoinCode 6 11 9 16
private def sf : Formula := .all 35
  (namedFilterBody 32 34 35 (Formula.member 33 35).not)
private def tf (a : Nat) : Formula := .all 37 (.all 38
  (.imp (.member a 37) (.imp (.member 37 38) (.member a 38))))

/-- The order clause with the actual new source and suffix names. -/
def newOrderAt : Formula := replace 8 40 (replace 7 38 newOrder)

private def vacuity (x : Nat) (hx : x ∈ [7,8]) :
    ∀ h, h ∈ orderContext → KDerivation (imp h (allCode x h)) := by
  intro h hh
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  simp only [orderContext,List.mem_cons,List.not_mem_nil,or_false] at hh
  by_cases ht : h = T
  · subst h
    have hv := (tf 32).vacuity x (by rcases hx with rfl | rfl <;> decide)
    simpa [tf,PASoundness.PAtoCompactAdditionSuccessorGraphMixed.targetTrans,
      transitiveCode,Formula.encode] using hv
  by_cases hs : h = S
  · subst h
    have hv := (tf 31).vacuity x (by rcases hx with rfl | rfl <;> decide)
    simpa [tf,PASoundness.PAtoCompactAdditionSuccessorGraphMixed.sourceTrans,
      transitiveCode,Formula.encode] using hv
  by_cases hf : h = F
  · subst h
    have hv := sf.vacuity x (by rcases hx with rfl | rfl <;> decide)
    simpa [sf,PASoundness.PAtoCompactAdditionSuccessorGraphClean.suffix,
      namedFilterBody,filterGraph,filterPredicate,namedBoth,Formula.not,Formula.encode,both,neg] using hv
  by_cases hp : h = P
  · subst h
    exact (pairFormula 11 31 32).vacuity x (by rcases hx with rfl | rfl <;> decide)
  by_cases ha : h = A
  · subst h
    have hv := (namedAdjoin 6 11 9 16).vacuity x (by rcases hx with rfl | rfl <;> decide)
    simpa [namedAdjoin,adjoinCode,namedBoth,namedEither,Formula.encode,both,neg,either] using hv
  by_cases hc : h = C
  · subst h
    exact PASoundness.PAtoCompactAdditionSuccessorGraphClean.oldClean.vacuity x
      (by rcases hx with rfl | rfl <;> decide)
  have ho : h = O := by simpa [ht,hs,hf,hp,ha,hc] using hh
  subst h
  exact PASoundness.PAtoCompactAdditionSuccessorOldOld.oldOrder.vacuity x
    (by rcases hx with rfl | rfl <;> decide)

/-- The exact new-domain order clause follows from the original seven
assumptions. -/
def order_at_new_domains : KDerivation (imp O (imp C (imp A (imp P (imp F
    (imp S (imp T newOrderAt.encode))))))) := by
  have hm : Context orderContext newOrder.encode := by
    have ho : Context orderContext O := .hypothesis (by simp [orderContext])
    have hc : Context orderContext C := .hypothesis (by simp [orderContext])
    have ha : Context orderContext A := .hypothesis (by simp [orderContext])
    have hp : Context orderContext P := .hypothesis (by simp [orderContext])
    have hf : Context orderContext F := .hypothesis (by simp [orderContext])
    have hs : Context orderContext S := .hypothesis (by simp [orderContext])
    have ht : Context orderContext T := .hypothesis (by simp [orderContext])
    exact .mp ht (.mp hs (.mp hf (.mp hp (.mp ha (.mp hc (.mp ho (.closed order_matrix)))))))
  have h7 := Context.generalize 7 (vacuity 7 (by decide)) hm
  have i7 := universalInstance 7 38 newOrder (by decide) (by decide) (by decide)
  have h38 : Context orderContext (replace 7 38 newOrder).encode := .mp h7 (.closed i7)
  have h8 := Context.generalize 8 (vacuity 8 (by decide)) h38
  have i8 := universalInstance 8 40 (replace 7 38 newOrder) (by decide) (by decide) (by decide)
  have hout : Context orderContext newOrderAt.encode := .mp h8 (.closed i8)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hout

theorem order_at_new_domains_certificate : theoremCode (certificate order_at_new_domains) =
    imp O (imp C (imp A (imp P (imp F (imp S (imp T newOrderAt.encode)))))) :=
  certificate_correct order_at_new_domains
end PASoundness.PAtoCompactAdditionOrderAtNewDomains
#print axioms PASoundness.PAtoCompactAdditionOrderAtNewDomains.order_at_new_domains
#print axioms PASoundness.PAtoCompactAdditionOrderAtNewDomains.order_at_new_domains_certificate
