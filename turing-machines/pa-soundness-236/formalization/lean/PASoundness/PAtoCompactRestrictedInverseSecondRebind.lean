import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactNamed

/-! Rebind the domain-restricted inverse-edge correspondence for the
complementary inverse-bijection clause. Both domain guards remain in the K
formulas. No inverse graph, bijection, symmetry, or interpretation is
constructed here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedInverseSecondRebind
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

def forwardBody : Formula :=
  .imp (conj (.member 1 3) (.member 0 2))
    (.imp (graphFormula 6 2 3) (graphFormula 7 3 2))

def reverseBody : Formula :=
  .imp (conj (.member 1 3) (.member 0 4))
    (.imp (graphFormula 7 3 4) (graphFormula 6 4 3))

def reverseDesired : Formula :=
  .imp (conj (.member 1 4) (.member 0 2))
    (.imp (graphFormula 7 4 2) (graphFormula 6 2 4))

/-- Commute the two universal binders, preserving the exact guard. -/
def rebind_forward : KDerivation
    (imp (allCode 3 (allCode 2 forwardBody.encode))
      (allCode 2 (allCode 3 forwardBody.encode))) :=
  allCommute 3 2 forwardBody.encode

theorem rebind_forward_certificate : theoremCode (certificate rebind_forward) =
    imp (allCode 3 (allCode 2 forwardBody.encode))
      (allCode 2 (allCode 3 forwardBody.encode)) := certificate_correct rebind_forward

/-- Rename the reverse edge's two variables, including their domain guards,
then commute their binders. Names 6,7 and pair-graph binders remain intact. -/
def rebind_reverse : KDerivation
    (imp (allCode 3 (allCode 4 reverseBody.encode))
      (allCode 2 (allCode 4 reverseDesired.encode))) := by
  let r1 := replace 4 2 reverseBody
  have h1 : KDerivation (imp (allCode 4 reverseBody.encode) (allCode 2 r1.encode)) := by
    exact (universalAlpha 4 2 reverseBody (by decide) (by decide) (by decide)).1
  have h2 : KDerivation (imp (allCode 3 (allCode 4 reverseBody.encode))
      (allCode 3 (allCode 2 r1.encode))) := allCongr 3 h1
  have h3 := (universalAlpha 3 4 (.all 2 r1) (by decide) (by decide) (by decide)).1
  have hr : replace 3 4 r1 = reverseDesired := by decide
  have h3' : KDerivation (imp (allCode 3 (allCode 2 r1.encode))
      (allCode 4 (allCode 2 reverseDesired.encode))) := by
    simpa [Formula.encode, replace, hr] using h3
  exact compose h2 (compose h3' (allCommute 4 2 reverseDesired.encode))

theorem rebind_reverse_certificate : theoremCode (certificate rebind_reverse) =
    imp (allCode 3 (allCode 4 reverseBody.encode))
      (allCode 2 (allCode 4 reverseDesired.encode)) := certificate_correct rebind_reverse

end PASoundness.PAtoCompactRestrictedInverseSecondRebind

#print axioms PASoundness.PAtoCompactRestrictedInverseSecondRebind.rebind_forward
#print axioms PASoundness.PAtoCompactRestrictedInverseSecondRebind.rebind_forward_certificate
#print axioms PASoundness.PAtoCompactRestrictedInverseSecondRebind.rebind_reverse
#print axioms PASoundness.PAtoCompactRestrictedInverseSecondRebind.rebind_reverse_certificate
