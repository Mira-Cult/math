import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactZeroSuccessor
import PASoundness.CompactQuantifiers

/-! A capture-safe forward-bijection instance at the distinct input name 7.
The given bijection and input membership are explicit hypotheses. Literal K
code 1 is `member 0 0`; no semantic soundness or quotient law is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactBijectionForwardAtSeven
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Literal forward witness body at input name 2, target name 3, codomain 1,
and graph 6, with uniqueness quantified at name 4. -/
def witnessAtTwo : Formula := namedBoth (.member 1 3) (namedBoth (graphFormula 6 2 3)
  (.all 4 (.imp (namedBoth (.member 1 4) (graphFormula 6 2 4)) (.equal 4 3))))

/-- The same witness after capture-safe replacement of the input by name 7. -/
def witnessAtSeven : Formula := namedBoth (.member 1 3) (namedBoth (graphFormula 6 7 3)
  (.all 4 (.imp (namedBoth (.member 1 4) (graphFormula 6 7 4)) (.equal 4 3))))

/-- The target-membership and graph-edge portion of that witness. -/
def imageAtSeven : Formula := namedBoth (.member 1 3) (graphFormula 6 7 3)

private def forwardClause : Formula := .all 2 (.imp (.member 0 2) (.ex 3 witnessAtTwo))

/-- From the exact supplied bijection and membership of 7 in source 0, K
constructs the entire forward witness at output name 3. All displayed
names are syntactic labels; the objects assigned to them may coincide. -/
def forward_witness_at_seven : KDerivation
    (imp bijectionFormula.encode (imp (member 0 7) (existsCode 3 witnessAtSeven.encode))) := by
  have hp : KDerivation (imp bijectionFormula.encode forwardClause.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    have hb : Context [bijectionFormula.encode] bijectionFormula.encode := .head [] _
    change Context [bijectionFormula.encode] (both forwardClause.encode _) at hb
    exact Context.conjunctionLeft hb
  have hi : KDerivation (imp forwardClause.encode
      (imp (member 0 7) (existsCode 3 witnessAtSeven.encode))) := by
    let f : Formula := .imp (.member 0 2) (.ex 3 witnessAtTwo)
    have h := CompactNamed.universalInstance 2 7 f (by decide) (by decide) (by decide)
    have hs : CompactNamed.replace 2 7 f =
        .imp (.member 0 7) (.ex 3 witnessAtSeven) := by decide
    simpa only [forwardClause, f, hs, Formula.encode] using h
  exact compose hp hi

/-- The same supplied hypotheses yield one target member and one represented
edge. The uniqueness part is discarded, while the same witness is retained. -/
def forward_image_at_seven : KDerivation
    (imp bijectionFormula.encode (imp (member 0 7) (existsCode 3 imageAtSeven.encode))) := by
  have hproj : KDerivation (imp witnessAtSeven.encode imageAtSeven.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let W := witnessAtSeven.encode
    have hw : Context [W] W := .head [] _
    have hm : Context [W] (member 1 3) := Context.conjunctionLeft hw
    have hg : Context [W] (graphFormula 6 7 3).encode :=
      Context.conjunctionLeft (Context.conjunctionRight hw)
    exact Context.conjunctionIntro hm hg
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 0 7,bijectionFormula.encode]
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ (member 0 7) := .head _ _
  have hw : Context Γ (existsCode 3 witnessAtSeven.encode) :=
    .mp hs (.mp hb (.closed forward_witness_at_seven))
  exact .mp hw (.closed (existsCongr 3 hproj))

theorem forward_witness_at_seven_certificate :
    theoremCode (certificate forward_witness_at_seven) =
      imp bijectionFormula.encode (imp (member 0 7) (existsCode 3 witnessAtSeven.encode)) :=
  certificate_correct forward_witness_at_seven

theorem forward_image_at_seven_certificate :
    theoremCode (certificate forward_image_at_seven) =
      imp bijectionFormula.encode (imp (member 0 7) (existsCode 3 imageAtSeven.encode)) :=
  certificate_correct forward_image_at_seven

end PASoundness.PAtoCompactBijectionForwardAtSeven

#print axioms PASoundness.PAtoCompactBijectionForwardAtSeven.forward_witness_at_seven
#print axioms PASoundness.PAtoCompactBijectionForwardAtSeven.forward_image_at_seven
#print axioms PASoundness.PAtoCompactBijectionForwardAtSeven.forward_witness_at_seven_certificate
#print axioms PASoundness.PAtoCompactBijectionForwardAtSeven.forward_image_at_seven_certificate
