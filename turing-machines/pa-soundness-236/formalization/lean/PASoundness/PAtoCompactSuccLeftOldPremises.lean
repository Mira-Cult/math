import PASoundness.PAtoCompactSuccBijectionPremises
import PASoundness.PAtoCompactSuccBijectionLeft
import PASoundness.PAtoCompactSuccLeftOldCaseClosed

/-! Project the exact eight supplied premises into the closed old-source
pointwise left-bijection case. No premise is asserted and no new graph or
quotient construction is claimed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccLeftOldPremises
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccBijectionPremises
open PASoundness.PAtoCompactSuccBijectionLeft PASoundness.PAtoCompactSuccLeftOldCaseClosed

/-- The named premise conjunction contains the source successor graph. -/
def source_from_premises : KDerivation (imp premisesCode sourceSuccessor) := by
  apply Context.closeEmpty
  apply Context.deduction
  have hp : Context [premisesCode] premisesCode := Context.head [] _
  exact Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hp))

/-- The actual old-source pointwise proof, under the shared premise code. -/
def old_from_premises : KDerivation (imp premisesCode (imp (member 0 2) pointGoal)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 0 2,premisesCode]
  have hm : Context Γ (member 0 2) := Context.head _ _
  have hp : Context Γ premisesCode := .hypothesis (by simp [Γ])
  have hM : Context Γ oldMatrix := Context.conjunctionLeft hp
  have htail1 := Context.conjunctionRight hp
  have hC : Context Γ cleanGraph := Context.conjunctionLeft htail1
  have htail2 := Context.conjunctionRight htail1
  have htail3 := Context.conjunctionRight htail2
  have hT : Context Γ targetSuccessor := Context.conjunctionLeft htail3
  have htail4 := Context.conjunctionRight htail3
  have hP : Context Γ newPair := Context.conjunctionLeft htail4
  have htail5 := Context.conjunctionRight htail4
  have hG : Context Γ newGraph := Context.conjunctionLeft htail5
  have htail6 := Context.conjunctionRight htail5
  have hR : Context Γ sourceIrreflexive := Context.conjunctionLeft htail6
  have hresult := Context.mp hm (.mp hP (.mp hG (.mp hT (.mp hR (.mp hC (.mp hM
    (.closed old_source_case_closed)))))))
  exact hresult

theorem old_from_premises_certificate : theoremCode (certificate old_from_premises) =
    imp premisesCode (imp (member 0 2) pointGoal) := certificate_correct old_from_premises

end PASoundness.PAtoCompactSuccLeftOldPremises

#print axioms PASoundness.PAtoCompactSuccLeftOldPremises.source_from_premises
#print axioms PASoundness.PAtoCompactSuccLeftOldPremises.old_from_premises
#print axioms PASoundness.PAtoCompactSuccLeftOldPremises.old_from_premises_certificate
