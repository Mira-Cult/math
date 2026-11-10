import PASoundness.PAtoCompactConditionalTransitivityUniqueness
import PASoundness.CompactQuantifiers

/-! The actual inverse-uniqueness clause yields a guarded local uniqueness
test. The existential preimage is alpha-renamed before eliminating it, so
the source name 2 remains free. This constructs no composition graph. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityFirstInverse
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityUniqueness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def secondBody : Formula := match bijectionFormula with
  | .imp (.imp _ (.imp (.all _ f) _)) _ => f
  | _ => .bottom

private def witnessBody : Formula := match secondBody with
  | .imp _ (.ex _ f) => f
  | _ => .bottom

private def at10 : Formula := replace 3 10 witnessBody
private def at12 : Formula := replace 2 12 at10
private def uniqueBody : Formula := .imp
  ((Formula.member 0 4).imp (graphFormula 6 4 10).not).not (.equal 4 12)

private def localGoal : Formula := .imp (.member 1 10)
  (.imp (.member 0 2) (.imp (.member 0 4)
    (.imp (graphFormula 6 2 10) (.imp (graphFormula 6 4 10) (.equal 2 4)))))

private theorem localGoal_encode : localGoal.encode = firstInverseUnique := by rfl

private def witness_to_unique : KDerivation (imp at12.encode firstInverseUnique) := by
  have h2 := universalInstance 4 2 uniqueBody (by decide) (by decide) (by decide)
  have h4 := allSpecialize 4 uniqueBody (by decide)
  have e2 : replace 4 2 uniqueBody = .imp
      ((Formula.member 0 2).imp (graphFormula 6 2 10).not).not (.equal 2 12) := by decide
  rw [e2] at h2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 4 10).encode, (graphFormula 6 2 10).encode,
    member 0 4, member 0 2, member 1 10, at12.encode]
  have hw : Context Γ at12.encode := .hypothesis (by simp [Γ])
  have hu : Context Γ (allCode 4 uniqueBody.encode) := by
    change Context Γ (both (member 0 12)
      (both (graphFormula 6 12 10).encode (allCode 4 uniqueBody.encode))) at hw
    exact Context.conjunctionRight (Context.conjunctionRight hw)
  have ha : Context Γ (member 0 2) := .hypothesis (by simp [Γ])
  have hb : Context Γ (member 0 4) := .hypothesis (by simp [Γ])
  have hg : Context Γ (graphFormula 6 2 10).encode := .hypothesis (by simp [Γ])
  have hh : Context Γ (graphFormula 6 4 10).encode := Context.head _ _
  have h2' : Context Γ (imp (both (member 0 2) (graphFormula 6 2 10).encode) (equal 2 12)) :=
    .mp hu (.closed h2)
  have h4' : Context Γ (imp (both (member 0 4) (graphFormula 6 4 10).encode) (equal 4 12)) :=
    .mp hu (.closed h4)
  have he : Context Γ (equal 2 12) := .mp (Context.conjunctionIntro ha hg) h2'
  have he' : Context Γ (equal 4 12) := .mp (Context.conjunctionIntro hb hh) h4'
  exact Context.eqTrans he (Context.eqSymm he')

/-- The actual second bijection conjunct entails the local guarded inverse
uniqueness test. The preimage binder is moved from 2 to the fresh name 12. -/
def first_inverse_unique_of_bijection : KDerivation
    (imp bijectionFormula.encode (imp (member 1 10) firstInverseUnique)) := by
  have hv : KDerivation (imp firstInverseUnique (allCode 12 firstInverseUnique)) := by
    simpa only [← localGoal_encode] using Formula.vacuity 12 localGoal (by decide)
  have helim : KDerivation (imp (existsCode 12 at12.encode) firstInverseUnique) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim hv (.closed (.generalize 12 witness_to_unique))
      (Context.head [] _)
  have halpha := (existentialAlpha 2 12 at10 (by decide) (by decide) (by decide)).1
  have hspec := universalInstance 3 10 secondBody (by decide) (by decide) (by decide)
  have hsecond : replace 3 10 secondBody = .imp (.member 1 10) (.ex 2 at10) := by decide
  rw [hsecond] at hspec
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 1 10, bijectionFormula.encode]
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 1 10) := Context.head _ _
  have hf : Context Γ (allCode 3 secondBody.encode) := by
    change Context Γ (both _ (allCode 3 secondBody.encode)) at hb
    exact Context.conjunctionRight hb
  have hi : Context Γ (imp (member 1 10) (existsCode 2 at10.encode)) := .mp hf (.closed hspec)
  have he : Context Γ (existsCode 2 at10.encode) := .mp hm hi
  have he' : Context Γ (existsCode 12 at12.encode) := .mp he (.closed halpha)
  exact .mp he' (.closed helim)

theorem first_inverse_unique_of_bijection_certificate :
    theoremCode (certificate first_inverse_unique_of_bijection) =
      imp bijectionFormula.encode (imp (member 1 10) firstInverseUnique) :=
  certificate_correct first_inverse_unique_of_bijection

end PASoundness.PAtoCompactConditionalTransitivityFirstInverse

#print axioms PASoundness.PAtoCompactConditionalTransitivityFirstInverse.first_inverse_unique_of_bijection
#print axioms PASoundness.PAtoCompactConditionalTransitivityFirstInverse.first_inverse_unique_of_bijection_certificate
