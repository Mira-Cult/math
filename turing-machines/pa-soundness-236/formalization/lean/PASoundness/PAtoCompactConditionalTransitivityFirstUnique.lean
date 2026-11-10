import PASoundness.PAtoCompactConditionalTransitivityUniqueness
import PASoundness.CompactQuantifiers

/-! Extract a local first-graph uniqueness test from the actual quantified
bijection clause. No composition graph or quotient transitivity is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityFirstUnique
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityUniqueness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def firstBody : Formula := match bijectionFormula with
  | .imp (.imp (.all _ f) _) _ => f
  | _ => .bottom

private def witnessBody : Formula := match firstBody with
  | .imp _ (.ex _ f) => f
  | _ => .bottom

private def uniqueBody : Formula := .imp
  ((Formula.member 1 4).imp (graphFormula 6 2 4).not).not (.equal 4 3)

private def localGoal : Formula := .imp (.member 0 2)
  (.imp (.member 1 10) (.imp (.member 1 11)
    (.imp (graphFormula 6 2 10) (.imp (graphFormula 6 2 11) (.equal 10 11)))))

private theorem localGoal_encode : localGoal.encode = firstUnique := by rfl

private def witness_to_unique : KDerivation (imp witnessBody.encode firstUnique) := by
  have h10 := universalInstance 4 10 uniqueBody (by decide) (by decide) (by decide)
  have h11 := universalInstance 4 11 uniqueBody (by decide) (by decide) (by decide)
  have e10 : replace 4 10 uniqueBody = .imp
      ((Formula.member 1 10).imp (graphFormula 6 2 10).not).not (.equal 10 3) := by decide
  have e11 : replace 4 11 uniqueBody = .imp
      ((Formula.member 1 11).imp (graphFormula 6 2 11).not).not (.equal 11 3) := by decide
  rw [e10] at h10
  rw [e11] at h11
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 2 11).encode, (graphFormula 6 2 10).encode,
    member 1 11, member 1 10, member 0 2, witnessBody.encode]
  have hw : Context Γ witnessBody.encode := .hypothesis (by simp [Γ])
  have hu : Context Γ (allCode 4 uniqueBody.encode) := by
    change Context Γ (both (member 1 3)
      (both (graphFormula 6 2 3).encode (allCode 4 uniqueBody.encode))) at hw
    exact Context.conjunctionRight (Context.conjunctionRight hw)
  have ha : Context Γ (member 1 10) := .hypothesis (by simp [Γ])
  have hb : Context Γ (member 1 11) := .hypothesis (by simp [Γ])
  have hg : Context Γ (graphFormula 6 2 10).encode := .hypothesis (by simp [Γ])
  have hh : Context Γ (graphFormula 6 2 11).encode := Context.head _ _
  have h10' : Context Γ (imp (both (member 1 10) (graphFormula 6 2 10).encode) (equal 10 3)) := by
    exact .mp hu (.closed h10)
  have h11' : Context Γ (imp (both (member 1 11) (graphFormula 6 2 11).encode) (equal 11 3)) := by
    exact .mp hu (.closed h11)
  have he : Context Γ (equal 10 3) := .mp (Context.conjunctionIntro ha hg) h10'
  have he' : Context Γ (equal 11 3) := .mp (Context.conjunctionIntro hb hh) h11'
  exact Context.eqTrans he (Context.eqSymm he')

/-- The actual first bijection clause supplies the local uniqueness test,
conditional on membership of the source in the left-hand domain. -/
def first_unique_of_bijection : KDerivation
    (imp bijectionFormula.encode (imp (member 0 2) firstUnique)) := by
  have hv : KDerivation (imp firstUnique (allCode 3 firstUnique)) := by
    simpa only [← localGoal_encode] using Formula.vacuity 3 localGoal (by decide)
  have helim : KDerivation (imp (existsCode 3 witnessBody.encode) firstUnique) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim hv (.closed (.generalize 3 witness_to_unique))
      (Context.head [] _)
  have hspec : KDerivation (imp (allCode 2 firstBody.encode) firstBody.encode) :=
    allSpecialize 2 firstBody (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 0 2, bijectionFormula.encode]
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 0 2) := Context.head _ _
  have hf : Context Γ (allCode 2 firstBody.encode) := by
    change Context Γ (both (allCode 2 firstBody.encode) _) at hb
    exact Context.conjunctionLeft hb
  have hi : Context Γ firstBody.encode := .mp hf (.closed hspec)
  have he : Context Γ (existsCode 3 witnessBody.encode) := .mp hm hi
  exact .mp he (.closed helim)

theorem first_unique_of_bijection_certificate :
    theoremCode (certificate first_unique_of_bijection) =
      imp bijectionFormula.encode (imp (member 0 2) firstUnique) :=
  certificate_correct first_unique_of_bijection

end PASoundness.PAtoCompactConditionalTransitivityFirstUnique

#print axioms PASoundness.PAtoCompactConditionalTransitivityFirstUnique.first_unique_of_bijection
#print axioms PASoundness.PAtoCompactConditionalTransitivityFirstUnique.first_unique_of_bijection_certificate
