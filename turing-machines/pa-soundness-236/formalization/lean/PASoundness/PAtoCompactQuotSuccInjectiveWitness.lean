import PASoundness.PAtoCompactQuotSuccWitnessLocal
import PASoundness.PAtoCompactTransitiveWitness

/-! Eliminate the two fresh quotient-successor witnesses from the checked
local cancellation. Endpoint equality guards and the quotient-output E premise
remain explicit; this is not yet an unguarded PA successor axiom. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotSuccInjectiveWitness
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactEquivalentAliasInstantiation PASoundness.PAtoCompactEquivalentAliasGuardLift
open PASoundness.PAtoCompactQuotSuccInjectiveRaw
open PASoundness.PAtoCompactQuotSuccWitnessFresh PASoundness.PAtoCompactQuotSuccWitnessLocal
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Remaining explicitly guarded endpoint implication. -/
def guardedGoal : Formula := .imp (.equal 40 2) (.imp (.equal 41 7)
  (.imp (.equal 42 5) (.imp (.equal 43 8) (.imp edge78 (guarded originalAliases)))))

/-- Place both fresh S bodies before the retained endpoint guards. -/
def reordered_local : KDerivation (imp secondFreshBody.encode
    (imp firstFreshBody.encode guardedGoal.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [edge78.encode,equal 43 8,equal 42 5,equal 41 7,equal 40 2,
    firstFreshBody.encode,secondFreshBody.encode]
  have h1 : Context Γ firstFreshBody.encode := .hypothesis (by simp [Γ])
  have h2 : Context Γ secondFreshBody.encode := .hypothesis (by simp [Γ])
  have h40 : Context Γ (equal 40 2) := .hypothesis (by simp [Γ])
  have h41 : Context Γ (equal 41 7) := .hypothesis (by simp [Γ])
  have h42 : Context Γ (equal 42 5) := .hypothesis (by simp [Γ])
  have h43 : Context Γ (equal 43 8) := .hypothesis (by simp [Γ])
  have hE : Context Γ edge78.encode := Context.head _ _
  exact .mp h2 (.mp h1 (.mp hE (.mp h43 (.mp h42 (.mp h41 (.mp h40 (.closed local_cancellation)))))))

/-- Eliminate the second fresh witness while the first is still fixed. -/
def second_witness_elim : KDerivation (imp secondAliases.encode
    (imp firstFreshBody.encode guardedGoal.encode)) := by
  let Q : Formula := .imp firstFreshBody guardedGoal
  have hfresh : 1 ∉ Q.names := by decide
  have hv : KDerivation (imp Q.encode (allCode 1 Q.encode)) := Q.vacuity 1 hfresh
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [secondAliases.encode]
  have hex : Context Γ (existsCode 1 secondFreshBody.encode) :=
    .mp (Context.head [] secondAliases.encode) (.closed second_witness_alpha)
  exact Context.existsElim hv (.closed (.generalize 1 reordered_local)) hex

/-- Eliminate both fresh witnesses, retaining all guards and output E. -/
def witnesses_eliminated : KDerivation (imp firstAliases.encode
    (imp secondAliases.encode guardedGoal.encode)) := by
  let Q : Formula := .imp secondAliases guardedGoal
  have hfresh : 0 ∉ Q.names := by decide
  have hv : KDerivation (imp Q.encode (allCode 0 Q.encode)) := Q.vacuity 0 hfresh
  have hlocal : KDerivation (imp firstFreshBody.encode Q.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [secondAliases.encode,firstFreshBody.encode]
    have ha : Context Γ firstFreshBody.encode := .hypothesis (by simp [Γ])
    have hb : Context Γ secondAliases.encode := Context.head _ _
    exact .mp ha (.mp hb (.closed second_witness_elim))
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [firstAliases.encode]
  have hex : Context Γ (existsCode 0 firstFreshBody.encode) :=
    .mp (Context.head [] firstAliases.encode) (.closed first_witness_alpha)
  exact Context.existsElim hv (.closed (.generalize 0 hlocal)) hex

theorem witnesses_eliminated_certificate : theoremCode (certificate witnesses_eliminated) =
    imp firstAliases.encode (imp secondAliases.encode guardedGoal.encode) :=
  certificate_correct witnesses_eliminated

end PASoundness.PAtoCompactQuotSuccInjectiveWitness

#print axioms PASoundness.PAtoCompactQuotSuccInjectiveWitness.witnesses_eliminated
#print axioms PASoundness.PAtoCompactQuotSuccInjectiveWitness.witnesses_eliminated_certificate
