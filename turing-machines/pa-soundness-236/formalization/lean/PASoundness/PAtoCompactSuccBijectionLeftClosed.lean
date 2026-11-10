import PASoundness.PAtoCompactSuccBijectionPremisesAtTwo
import PASoundness.PAtoCompactSuccLeftOldPremises
import PASoundness.PAtoCompactSuccLeftTopFinal

/-! Actual K proof of the first successor-bijection clause under the exact
shared premise conjunction. The supplied old matrix, clean graph, successor,
adjunction, pair and encoded irreflexivity remain explicit in premisesCode;
no graph collection or unconditional quotient congruence is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccBijectionLeftClosed
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccBijectionPremises
open PASoundness.PAtoCompactSuccBijectionPremisesAtTwo PASoundness.PAtoCompactSuccBijectionLeft
open PASoundness.PAtoCompactSuccLeftOldPremises PASoundness.PAtoCompactSuccLeftTopFinal

/-- Project and apply the closed top-source proof under all shared premises. -/
def top_from_premises : KDerivation (imp premisesCode (imp (equal 2 0) pointGoal)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal 2 0,premisesCode]
  have he : Context Γ (equal 2 0) := Context.head _ _
  have hp : Context Γ premisesCode := .hypothesis (by simp [Γ])
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
  exact .mp he (.mp hP (.mp hG (.mp hT (.mp hR (.mp hC (.closed top_case_final))))))

/-- Both actual point cases give the exact new left-bijection clause. -/
def left_closed : KDerivation (imp premisesCode leftFormula.encode) :=
  left_from_cases premisesCode premises_vacuity_2 source_from_premises old_from_premises top_from_premises

theorem left_closed_certificate : theoremCode (certificate left_closed) =
    imp premisesCode leftFormula.encode := certificate_correct left_closed

end PASoundness.PAtoCompactSuccBijectionLeftClosed

#print axioms PASoundness.PAtoCompactSuccBijectionLeftClosed.top_from_premises
#print axioms PASoundness.PAtoCompactSuccBijectionLeftClosed.left_closed
#print axioms PASoundness.PAtoCompactSuccBijectionLeftClosed.left_closed_certificate
