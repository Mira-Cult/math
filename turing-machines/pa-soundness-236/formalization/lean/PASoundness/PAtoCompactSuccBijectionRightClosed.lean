import PASoundness.PAtoCompactSuccBijectionRightTopCompose
import PASoundness.PAtoCompactSuccRightOldCase

/-! The exact right/preimage clause for supplied-clean-graph successor
congruence, assembled from the checked old-target and new-endpoint cases.
Every source graph, successor, new pair/adjunction and encoded-irreflexivity
assumption remains explicit in premisesCode. This does not establish graph
existence, the left bijection clause, order preservation, or a quotient. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccBijectionRightClosed
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccBijectionPremises
open PASoundness.PAtoCompactSuccBijectionRight PASoundness.PAtoCompactSuccBijectionRightTopCompose
open PASoundness.PAtoCompactSuccRightOldCase

/-- The full displayed premises give the old-target right-clause witness. -/
def old_from_premises : KDerivation
    (imp premisesCode (imp (member 1 28) (rightBody 28).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 1 28,premisesCode]
  have hp : Context Γ premisesCode := .hypothesis (by simp [Γ])
  have ht : Context Γ (member 1 28) := Context.head _ _
  have hm : Context Γ oldMatrix := Context.conjunctionLeft hp
  have h1 := Context.conjunctionRight hp
  have hc : Context Γ cleanGraph := Context.conjunctionLeft h1
  have h2 := Context.conjunctionRight h1
  have hs : Context Γ sourceSuccessor := Context.conjunctionLeft h2
  have h3 := Context.conjunctionRight h2
  have h4 := Context.conjunctionRight h3
  have hpair : Context Γ newPair := Context.conjunctionLeft h4
  have h5 := Context.conjunctionRight h4
  have hgraph : Context Γ newGraph := Context.conjunctionLeft h5
  have h6 := Context.conjunctionRight h5
  have hirr : Context Γ targetIrreflexive := Context.conjunctionRight h6
  exact .mp ht (.mp hpair (.mp hgraph (.mp hirr (.mp hs (.mp hc (.mp hm
    (.closed old_target_case_from_data)))))))

/-- From exactly the supplied eight-premise conjunction, K derives the renamed
right bijection clause. The old/top pointwise K interfaces are both supplied
by checked derivations; no unproved proof-data premise remains. -/
def right_closed : KDerivation (imp premisesCode rightClause.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  have hp : Context [premisesCode] premisesCode := Context.head [] _
  have h1 := Context.conjunctionRight hp
  have h2 := Context.conjunctionRight h1
  have h3 := Context.conjunctionRight h2
  have ht : Context [premisesCode] targetSuccessor := Context.conjunctionLeft h3
  have h := right_from_cases premisesCode premises_vacuity_28 old_from_premises top_from_premises
  exact .mp ht (.mp hp (.closed h))

theorem right_closed_certificate : theoremCode (certificate right_closed) =
    imp premisesCode rightClause.encode := certificate_correct right_closed

end PASoundness.PAtoCompactSuccBijectionRightClosed

#print axioms PASoundness.PAtoCompactSuccBijectionRightClosed.old_from_premises
#print axioms PASoundness.PAtoCompactSuccBijectionRightClosed.right_closed
#print axioms PASoundness.PAtoCompactSuccBijectionRightClosed.right_closed_certificate
