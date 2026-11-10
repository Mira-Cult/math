import PASoundness.PAtoCompactConditionalTransitivityUniqueness
import PASoundness.CompactQuantifiers

/-! Extract the two local uniqueness conditions for the second isomorphism
from its literal renamed bijection clause. No graph composition is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivitySecondUnique
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityUniqueness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The second bijection has domain 1, codomain 8, and graph 7. -/
def secondBijection : Formula := replace 6 7 (replace 0 1 (replace 1 8 bijectionFormula))

private def firstBody : Formula := match secondBijection with
  | .imp (.imp (.all _ f) _) _ => f
  | _ => .bottom
private def firstWitness : Formula := match firstBody with
  | .imp _ (.ex _ f) => f
  | _ => .bottom
private def firstAt10 : Formula := replace 2 10 firstWitness
private def firstAt12 : Formula := replace 3 12 firstAt10
private def forwardBody : Formula := .imp
  ((Formula.member 8 4).imp (graphFormula 7 10 4).not).not (.equal 4 12)
private def forwardGoal : Formula := .imp (.member 1 10)
  (.imp (.member 8 3) (.imp (.member 8 5)
    (.imp (graphFormula 7 10 3) (.imp (graphFormula 7 10 5) (.equal 3 5)))))
private theorem forwardGoal_encode : forwardGoal.encode = secondUnique := by rfl

private def forward_witness_to_unique : KDerivation (imp firstAt12.encode secondUnique) := by
  have h3 := universalInstance 4 3 forwardBody (by decide) (by decide) (by decide)
  have h5 := universalInstance 4 5 forwardBody (by decide) (by decide) (by decide)
  have e3 : replace 4 3 forwardBody = .imp
      ((Formula.member 8 3).imp (graphFormula 7 10 3).not).not (.equal 3 12) := by decide
  have e5 : replace 4 5 forwardBody = .imp
      ((Formula.member 8 5).imp (graphFormula 7 10 5).not).not (.equal 5 12) := by decide
  rw [e3] at h3
  rw [e5] at h5
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 7 10 5).encode, (graphFormula 7 10 3).encode,
    member 8 5, member 8 3, member 1 10, firstAt12.encode]
  have hw : Context Γ firstAt12.encode := .hypothesis (by simp [Γ])
  have hu : Context Γ (allCode 4 forwardBody.encode) := by
    change Context Γ (both (member 8 12)
      (both (graphFormula 7 10 12).encode (allCode 4 forwardBody.encode))) at hw
    exact Context.conjunctionRight (Context.conjunctionRight hw)
  have ha : Context Γ (member 8 3) := .hypothesis (by simp [Γ])
  have hb : Context Γ (member 8 5) := .hypothesis (by simp [Γ])
  have hg : Context Γ (graphFormula 7 10 3).encode := .hypothesis (by simp [Γ])
  have hh : Context Γ (graphFormula 7 10 5).encode := Context.head _ _
  have h3' : Context Γ (imp (both (member 8 3) (graphFormula 7 10 3).encode) (equal 3 12)) :=
    .mp hu (.closed h3)
  have h5' : Context Γ (imp (both (member 8 5) (graphFormula 7 10 5).encode) (equal 5 12)) :=
    .mp hu (.closed h5)
  have he : Context Γ (equal 3 12) := .mp (Context.conjunctionIntro ha hg) h3'
  have he' : Context Γ (equal 5 12) := .mp (Context.conjunctionIntro hb hh) h5'
  exact Context.eqTrans he (Context.eqSymm he')

/-- The literal second-graph image clause yields its guarded local forward
uniqueness instance, alpha-renaming the image witness 3 to fresh 12. -/
def second_unique_of_bijection : KDerivation
    (imp secondBijection.encode (imp (member 1 10) secondUnique)) := by
  have hv : KDerivation (imp secondUnique (allCode 12 secondUnique)) := by
    simpa only [← forwardGoal_encode] using Formula.vacuity 12 forwardGoal (by decide)
  have helim : KDerivation (imp (existsCode 12 firstAt12.encode) secondUnique) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim hv (.closed (.generalize 12 forward_witness_to_unique))
      (Context.head [] _)
  have halpha := (existentialAlpha 3 12 firstAt10 (by decide) (by decide) (by decide)).1
  have hspec := universalInstance 2 10 firstBody (by decide) (by decide) (by decide)
  have hfirst : replace 2 10 firstBody = .imp (.member 1 10) (.ex 3 firstAt10) := by decide
  rw [hfirst] at hspec
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 1 10, secondBijection.encode]
  have hb : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 1 10) := Context.head _ _
  have hf : Context Γ (allCode 2 firstBody.encode) := by
    change Context Γ (both (allCode 2 firstBody.encode) _) at hb
    exact Context.conjunctionLeft hb
  have hi : Context Γ (imp (member 1 10) (existsCode 3 firstAt10.encode)) := .mp hf (.closed hspec)
  have he : Context Γ (existsCode 3 firstAt10.encode) := .mp hm hi
  have he' : Context Γ (existsCode 12 firstAt12.encode) := .mp he (.closed halpha)
  exact .mp he' (.closed helim)

private def secondBody : Formula := match secondBijection with
  | .imp (.imp _ (.imp (.all _ f) _)) _ => f
  | _ => .bottom
private def secondWitness : Formula := match secondBody with
  | .imp _ (.ex _ f) => f
  | _ => .bottom
private def inverseBody : Formula := .imp
  ((Formula.member 1 4).imp (graphFormula 7 4 3).not).not (.equal 4 2)
private def inverseGoal : Formula := .imp (.member 8 3)
  (.imp (.member 1 10) (.imp (.member 1 11)
    (.imp (graphFormula 7 10 3) (.imp (graphFormula 7 11 3) (.equal 10 11)))))
private theorem inverseGoal_encode : inverseGoal.encode = secondInverseUnique := by rfl

private def inverse_witness_to_unique : KDerivation (imp secondWitness.encode secondInverseUnique) := by
  have h10 := universalInstance 4 10 inverseBody (by decide) (by decide) (by decide)
  have h11 := universalInstance 4 11 inverseBody (by decide) (by decide) (by decide)
  have e10 : replace 4 10 inverseBody = .imp
      ((Formula.member 1 10).imp (graphFormula 7 10 3).not).not (.equal 10 2) := by decide
  have e11 : replace 4 11 inverseBody = .imp
      ((Formula.member 1 11).imp (graphFormula 7 11 3).not).not (.equal 11 2) := by decide
  rw [e10] at h10
  rw [e11] at h11
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 7 11 3).encode, (graphFormula 7 10 3).encode,
    member 1 11, member 1 10, member 8 3, secondWitness.encode]
  have hw : Context Γ secondWitness.encode := .hypothesis (by simp [Γ])
  have hu : Context Γ (allCode 4 inverseBody.encode) := by
    change Context Γ (both (member 1 2)
      (both (graphFormula 7 2 3).encode (allCode 4 inverseBody.encode))) at hw
    exact Context.conjunctionRight (Context.conjunctionRight hw)
  have ha : Context Γ (member 1 10) := .hypothesis (by simp [Γ])
  have hb : Context Γ (member 1 11) := .hypothesis (by simp [Γ])
  have hg : Context Γ (graphFormula 7 10 3).encode := .hypothesis (by simp [Γ])
  have hh : Context Γ (graphFormula 7 11 3).encode := Context.head _ _
  have h10' : Context Γ (imp (both (member 1 10) (graphFormula 7 10 3).encode) (equal 10 2)) :=
    .mp hu (.closed h10)
  have h11' : Context Γ (imp (both (member 1 11) (graphFormula 7 11 3).encode) (equal 11 2)) :=
    .mp hu (.closed h11)
  have he : Context Γ (equal 10 2) := .mp (Context.conjunctionIntro ha hg) h10'
  have he' : Context Γ (equal 11 2) := .mp (Context.conjunctionIntro hb hh) h11'
  exact Context.eqTrans he (Context.eqSymm he')

/-- The literal second-graph preimage clause yields its guarded local inverse
uniqueness instance. -/
def second_inverse_unique_of_bijection : KDerivation
    (imp secondBijection.encode (imp (member 8 3) secondInverseUnique)) := by
  have hv : KDerivation (imp secondInverseUnique (allCode 2 secondInverseUnique)) := by
    simpa only [← inverseGoal_encode] using Formula.vacuity 2 inverseGoal (by decide)
  have helim : KDerivation (imp (existsCode 2 secondWitness.encode) secondInverseUnique) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim hv (.closed (.generalize 2 inverse_witness_to_unique))
      (Context.head [] _)
  have hspec : KDerivation (imp (allCode 3 secondBody.encode) secondBody.encode) :=
    allSpecialize 3 secondBody (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 8 3, secondBijection.encode]
  have hb : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 8 3) := Context.head _ _
  have hf : Context Γ (allCode 3 secondBody.encode) := by
    change Context Γ (both _ (allCode 3 secondBody.encode)) at hb
    exact Context.conjunctionRight hb
  have hi : Context Γ secondBody.encode := .mp hf (.closed hspec)
  have he : Context Γ (existsCode 2 secondWitness.encode) := .mp hm hi
  exact .mp he (.closed helim)

theorem second_unique_of_bijection_certificate :
    theoremCode (certificate second_unique_of_bijection) =
      imp secondBijection.encode (imp (member 1 10) secondUnique) :=
  certificate_correct second_unique_of_bijection

theorem second_inverse_unique_of_bijection_certificate :
    theoremCode (certificate second_inverse_unique_of_bijection) =
      imp secondBijection.encode (imp (member 8 3) secondInverseUnique) :=
  certificate_correct second_inverse_unique_of_bijection

end PASoundness.PAtoCompactConditionalTransitivitySecondUnique

#print axioms PASoundness.PAtoCompactConditionalTransitivitySecondUnique.second_unique_of_bijection
#print axioms PASoundness.PAtoCompactConditionalTransitivitySecondUnique.second_inverse_unique_of_bijection
#print axioms PASoundness.PAtoCompactConditionalTransitivitySecondUnique.second_unique_of_bijection_certificate
#print axioms PASoundness.PAtoCompactConditionalTransitivitySecondUnique.second_inverse_unique_of_bijection_certificate
