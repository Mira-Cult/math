import PASoundness.PAtoCompactSuccBijectionPremisesAtTwo
import PASoundness.PAtoCompactSuccBijectionLeft
import PASoundness.PAtoCompactSuccBijectionRight

/-! Conditional assembly of the literal successor-bijection matrix. Four
pointwise case derivations are explicit proof-data inputs. This is not a
proof that those cases, graph collection, quotient congruence or PA
soundness are available. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccCongruenceBijection
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.PAtoCompactSuccBijectionPremises PASoundness.PAtoCompactSuccBijectionPremisesAtTwo

/-- The left and right assemblers use the same exact first named conjunct. -/
theorem left_alignment : PAtoCompactSuccBijectionLeft.leftFormula =
    PAtoCompactSuccBijectionRight.leftClause := by decide

/-- The supplied eight-premise conjunction projects its source successor. -/
def source_successor_from_premises : KDerivation (imp premisesCode sourceSuccessor) := by
  apply Context.closeEmpty
  apply Context.deduction
  have hp : Context [premisesCode] premisesCode := Context.head [] premisesCode
  exact Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hp))

/-- The supplied eight-premise conjunction projects its target successor. -/
def target_successor_from_premises : KDerivation (imp premisesCode targetSuccessor) := by
  apply Context.closeEmpty
  apply Context.deduction
  have hp : Context [premisesCode] premisesCode := Context.head [] premisesCode
  exact Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hp)))

/-- Assemble exact successor bijectivity under the common assumptions and
four explicitly supplied old/top pointwise K derivations. -/
def bijection_from_cases
    (leftOld : KDerivation (imp premisesCode (imp (member 0 2) PAtoCompactSuccBijectionLeft.pointGoal)))
    (leftTop : KDerivation (imp premisesCode (imp (equal 2 0) PAtoCompactSuccBijectionLeft.pointGoal)))
    (rightOld : KDerivation (imp premisesCode (imp (member 1 28) (PAtoCompactSuccBijectionRight.rightBody 28).encode)))
    (rightTop : KDerivation (imp premisesCode (imp (equal 28 1) (PAtoCompactSuccBijectionRight.rightBody 28).encode))) :
    KDerivation (imp premisesCode newBijection.encode) := by
  let P := premisesCode
  have hl := PAtoCompactSuccBijectionLeft.left_from_cases P premises_vacuity_2
    source_successor_from_premises leftOld leftTop
  have hr := PAtoCompactSuccBijectionRight.right_from_cases P premises_vacuity_28 rightOld rightTop
  apply Context.closeEmpty
  apply Context.deduction
  have hp : Context [P] P := Context.head [] P
  have hleft : Context [P] PAtoCompactSuccBijectionRight.leftClause.encode := by
    rw [← left_alignment]
    exact .mp hp (.closed hl)
  have hright : Context [P] PAtoCompactSuccBijectionRight.rightClause.encode :=
    .mp (.mp hp (.closed target_successor_from_premises)) (.mp hp (.closed hr))
  rw [PAtoCompactSuccBijectionRight.new_bijection_alignment]
  exact Context.conjunctionIntro hleft hright

theorem bijection_from_cases_certificate
    (leftOld : KDerivation (imp premisesCode (imp (member 0 2) PAtoCompactSuccBijectionLeft.pointGoal)))
    (leftTop : KDerivation (imp premisesCode (imp (equal 2 0) PAtoCompactSuccBijectionLeft.pointGoal)))
    (rightOld : KDerivation (imp premisesCode (imp (member 1 28) (PAtoCompactSuccBijectionRight.rightBody 28).encode)))
    (rightTop : KDerivation (imp premisesCode (imp (equal 28 1) (PAtoCompactSuccBijectionRight.rightBody 28).encode))) :
    theoremCode (certificate (bijection_from_cases leftOld leftTop rightOld rightTop)) =
      imp premisesCode newBijection.encode :=
  certificate_correct (bijection_from_cases leftOld leftTop rightOld rightTop)

end PASoundness.PAtoCompactSuccCongruenceBijection

#print axioms PASoundness.PAtoCompactSuccCongruenceBijection.bijection_from_cases
#print axioms PASoundness.PAtoCompactSuccCongruenceBijection.bijection_from_cases_certificate
