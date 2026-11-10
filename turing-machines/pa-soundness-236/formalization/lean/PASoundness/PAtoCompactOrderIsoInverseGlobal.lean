import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactQuantifiers

/-! Capture-safe local instances of the supplied inverse-graph correspondence.
The displayed family is definitionally the reverse family in
PAtoCompactInverseBijection; it remains a hypothesis, not a graph construction. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactOrderIsoInverseGlobal
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def reverseBody : Formula := .imp (graphFormula 7 3 4) (graphFormula 6 4 3)
def reverseFamily : Formula := .all 3 (.all 4 reverseBody)
def atFirst : Formula := .imp (graphFormula 7 3 2) (graphFormula 6 2 3)
def atSecond : Formula := .imp (graphFormula 7 5 4) (graphFormula 6 4 5)

/-- The supplied global inverse family gives the two distinct graph instances
needed by the order matrix. Names 2,3,4,5,6,7 are disjoint from graph binders. -/
def global_reverse_instances : KDerivation
    (imp reverseFamily.encode (both atFirst.encode atSecond.encode)) := by
  have hi₃ := allSpecialize 3 (.all 4 reverseBody) (by decide)
  have hi₄ := universalInstance 4 2 reverseBody (by decide) (by decide) (by decide)
  have first : KDerivation (imp reverseFamily.encode atFirst.encode) := by
    have h : KDerivation (imp (allCode 4 reverseBody.encode) atFirst.encode) := by
      have he : replace 4 2 reverseBody = atFirst := by decide
      rw [he] at hi₄
      exact hi₄
    exact compose hi₃ h
  have hj₃ := universalInstance 3 5 (.all 4 reverseBody) (by decide) (by decide) (by decide)
  have second : KDerivation (imp reverseFamily.encode atSecond.encode) := by
    have h : KDerivation (imp reverseFamily.encode (allCode 4 atSecond.encode)) := by
      have he : replace 3 5 (.all 4 reverseBody) = .all 4 atSecond := by decide
      rw [he] at hj₃
      exact hj₃
    exact compose h (allSpecialize 4 atSecond (by decide))
  apply Context.closeEmpty
  apply Context.deduction
  have hr : Context [reverseFamily.encode] reverseFamily.encode := Context.head [] _
  exact Context.conjunctionIntro (.mp hr (.closed first)) (.mp hr (.closed second))

theorem global_reverse_instances_certificate :
    theoremCode (certificate global_reverse_instances) =
      imp reverseFamily.encode (both atFirst.encode atSecond.encode) :=
  certificate_correct global_reverse_instances

end PASoundness.PAtoCompactOrderIsoInverseGlobal

#print axioms PASoundness.PAtoCompactOrderIsoInverseGlobal.global_reverse_instances
#print axioms PASoundness.PAtoCompactOrderIsoInverseGlobal.global_reverse_instances_certificate
