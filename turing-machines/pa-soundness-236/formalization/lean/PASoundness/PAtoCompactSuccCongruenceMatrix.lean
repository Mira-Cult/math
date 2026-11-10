import PASoundness.PAtoCompactSuccBijectionClosed
import PASoundness.PAtoCompactSuccCongruenceOrder

/-! Assemble the K successor-isomorphism matrix from explicit supplied old
matrix, clean graph, successor, pair and adjunction witnesses. The two
relative nonself formulas are K theorems and are discharged syntactically.
The endpoint does not construct/restrict an arbitrary old graph, build the
witnesses, prove a quotient congruence, or give PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccCongruenceMatrix
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccBijectionPremises
open PASoundness.PAtoCompactSuccBijectionClosed PASoundness.PAtoCompactSuccCongruenceOrder
open PASoundness.PAtoCompactSuccCongruenceMixedOrder PASoundness.PAtoCompactTransitiveClosure

/-- Supplied semantic-free K formulas, omitting the two encoded nonself
formulas which K separately derives. -/
def corePremises : Nat := both oldMatrix (both cleanGraph
  (both sourceSuccessor (both targetSuccessor (both newPair newGraph))))

/-- The core assumptions supply the full bijection premise package; compact
nonself formulas are discharged using actual finite K proof data. -/
def premises_from_core : KDerivation (imp corePremises premisesCode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [corePremises]
  have hc : Context Γ corePremises := Context.head [] _
  have hm : Context Γ oldMatrix := Context.conjunctionLeft hc
  have h1 := Context.conjunctionRight hc
  have hg : Context Γ cleanGraph := Context.conjunctionLeft h1
  have h2 := Context.conjunctionRight h1
  have hs : Context Γ sourceSuccessor := Context.conjunctionLeft h2
  have h3 := Context.conjunctionRight h2
  have ht : Context Γ targetSuccessor := Context.conjunctionLeft h3
  have h4 := Context.conjunctionRight h3
  have hp : Context Γ newPair := Context.conjunctionLeft h4
  have ha : Context Γ newGraph := Context.conjunctionRight h4
  have hn0 : Context Γ sourceIrreflexive := .closed (self_membership_implies_code_one 0)
  have hn1 : Context Γ targetIrreflexive := .closed (self_membership_implies_code_one 1)
  exact Context.conjunctionIntro hm (Context.conjunctionIntro hg
    (Context.conjunctionIntro hs (Context.conjunctionIntro ht (Context.conjunctionIntro hp
      (Context.conjunctionIntro ha (Context.conjunctionIntro hn0 hn1))))))

/-- Under the exact supplied matrix, clean graph and local graph witnesses,
with both old domains explicitly transitive, derive the exact renamed
bijection-and-order matrix for their successors. -/
def successor_matrix : KDerivation (imp corePremises
    (imp sourceTrans (imp targetTrans newMatrix))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [targetTrans,sourceTrans,corePremises]
  have hc : Context Γ corePremises := .hypothesis (by simp [Γ])
  have hs : Context Γ sourceTrans := .hypothesis (by simp [Γ])
  have ht : Context Γ targetTrans := Context.head _ _
  have hp : Context Γ premisesCode := .mp hc (.closed premises_from_core)
  have hb : Context Γ newBijection.encode := .mp hp (.closed bijection_closed)
  have ho : Context Γ newOrder.encode := .mp ht (.mp hs (.mp hp (.closed order_closed)))
  exact Context.conjunctionIntro hb ho

theorem successor_matrix_certificate : theoremCode (certificate successor_matrix) =
    imp corePremises (imp sourceTrans (imp targetTrans newMatrix)) :=
  certificate_correct successor_matrix

end PASoundness.PAtoCompactSuccCongruenceMatrix

#print axioms PASoundness.PAtoCompactSuccCongruenceMatrix.premises_from_core
#print axioms PASoundness.PAtoCompactSuccCongruenceMatrix.successor_matrix
#print axioms PASoundness.PAtoCompactSuccCongruenceMatrix.successor_matrix_certificate
