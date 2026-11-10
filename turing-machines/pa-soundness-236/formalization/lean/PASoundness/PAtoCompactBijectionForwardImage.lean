import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactZeroSuccessor
import PASoundness.CompactQuantifiers

/-! Forward image extraction from the exact represented K bijection clause.
The input and output names are syntactic labels; their values may coincide.
The encoded negation uses literal code 1, i.e. membership of name 0 in itself. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactBijectionForwardImage
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The literal matrix of the forward bijection witness: codomain 1, input 2,
output 3, graph 6, and uniqueness binder 4. -/
def witness3 : Formula := namedBoth (.member 1 3) (namedBoth (graphFormula 6 2 3)
  (.all 4 (.imp (namedBoth (.member 1 4) (graphFormula 6 2 4)) (.equal 4 3))))

/-- A codomain-guarded edge, without the uniqueness component. -/
def image3 : Formula := namedBoth (.member 1 3) (graphFormula 6 2 3)

private def forwardClause : Formula := .all 2 (.imp (.member 0 2) (.ex 3 witness3))

/-- The actual K bijection formula supplies the exact forward witness for an
input in source 0. This is not a graph construction or a quotient theorem. -/
def forward_witness : KDerivation
    (imp bijectionFormula.encode (imp (member 0 2) (existsCode 3 witness3.encode))) := by
  have hp : KDerivation (imp bijectionFormula.encode forwardClause.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    have hb : Context [bijectionFormula.encode] bijectionFormula.encode := .head [] _
    change Context [bijectionFormula.encode] (both forwardClause.encode _) at hb
    exact Context.conjunctionLeft hb
  have hi : KDerivation (imp forwardClause.encode
      (imp (member 0 2) (existsCode 3 witness3.encode))) := by
    let f : Formula := .imp (.member 0 2) (.ex 3 witness3)
    have h := CompactNamed.allSpecialize 2 f (by decide)
    simpa only [forwardClause, f, Formula.encode] using h
  exact compose hp hi

/-- Discarding uniqueness, the same input has a represented edge to some
member of the target. The existential binder remains the literal name 3. -/
def forward_image : KDerivation
    (imp bijectionFormula.encode (imp (member 0 2) (existsCode 3 image3.encode))) := by
  have hproj : KDerivation (imp witness3.encode image3.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let W := witness3.encode
    have hw : Context [W] W := .head [] _
    have hm : Context [W] (member 1 3) := Context.conjunctionLeft hw
    have hg : Context [W] (graphFormula 6 2 3).encode :=
      Context.conjunctionLeft (Context.conjunctionRight hw)
    exact Context.conjunctionIntro hm hg
  have hlift : KDerivation (imp (existsCode 3 witness3.encode)
      (existsCode 3 image3.encode)) := existsCongr 3 hproj
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 0 2, bijectionFormula.encode]
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ (member 0 2) := .head _ _
  have hw : Context Γ (existsCode 3 witness3.encode) := .mp hs (.mp hb (.closed forward_witness))
  exact .mp hw (.closed hlift)

theorem forward_witness_certificate : theoremCode (certificate forward_witness) =
    imp bijectionFormula.encode (imp (member 0 2) (existsCode 3 witness3.encode)) :=
  certificate_correct forward_witness

theorem forward_image_certificate : theoremCode (certificate forward_image) =
    imp bijectionFormula.encode (imp (member 0 2) (existsCode 3 image3.encode)) :=
  certificate_correct forward_image

end PASoundness.PAtoCompactBijectionForwardImage

#print axioms PASoundness.PAtoCompactBijectionForwardImage.forward_witness
#print axioms PASoundness.PAtoCompactBijectionForwardImage.forward_image
#print axioms PASoundness.PAtoCompactBijectionForwardImage.forward_witness_certificate
#print axioms PASoundness.PAtoCompactBijectionForwardImage.forward_image_certificate
