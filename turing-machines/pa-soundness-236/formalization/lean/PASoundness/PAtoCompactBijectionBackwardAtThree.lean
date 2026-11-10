import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactZeroSuccessor
import PASoundness.CompactQuantifiers

/-! Backward graph-witness extraction from the exact K bijection clause.
The supplied graph and bijection are assumptions, not constructed here.
Compact negation uses literal code 1, namely `member 0 0`. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactBijectionBackwardAtThree
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Exact backward-bijection witness with source set 0, target 3, graph 6,
and a unique-source test bound at 4. -/
def witness (i : Nat) : Formula := namedBoth (.member 0 i)
  (namedBoth (graphFormula 6 i 3)
    (.all 4 (.imp (namedBoth (.member 0 4) (graphFormula 6 4 3)) (.equal 4 i))))

/-- The graph edge and its source guard, omitting the uniqueness clause. -/
def preimage : Formula := namedBoth (.member 0 7) (graphFormula 6 7 3)

private def backwardClause : Formula :=
  .all 3 (.imp (.member 1 3) (.ex 2 (witness 2)))

/-- From the actual bijection matrix and 3∈1, K constructs a witness at 7
for the exact reverse clause. Labels 0,1,3,4,6,7 and internal binders are
syntactically fixed; the values denoted by those labels may coincide. -/
def backward_witness : KDerivation
    (imp bijectionFormula.encode (imp (member 1 3) (existsCode 7 (witness 7).encode))) := by
  have hp : KDerivation (imp bijectionFormula.encode backwardClause.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    have hb : Context [bijectionFormula.encode] bijectionFormula.encode := .head [] _
    change Context [bijectionFormula.encode] (both _ backwardClause.encode) at hb
    exact Context.conjunctionRight hb
  have hi : KDerivation (imp backwardClause.encode
      (imp (member 1 3) (existsCode 2 (witness 2).encode))) := by
    let f : Formula := .imp (.member 1 3) (.ex 2 (witness 2))
    have h := CompactNamed.allSpecialize 3 f (by decide)
    simpa only [backwardClause, f, Formula.encode] using h
  have ha : KDerivation (imp (existsCode 2 (witness 2).encode)
      (existsCode 7 (witness 7).encode)) := by
    have h := (CompactNamed.existentialAlpha 2 7 (witness 2)
      (by decide) (by decide) (by decide)).1
    have hs : CompactNamed.replace 2 7 (witness 2) = witness 7 := by decide
    simpa only [hs] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 1 3, bijectionFormula.encode]
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 1 3) := .head _ _
  have hw : Context Γ (existsCode 2 (witness 2).encode) := .mp hm (.mp hb (.closed (compose hp hi)))
  exact .mp hw (.closed ha)

/-- Retaining the same preimage witness while discarding its uniqueness
component yields an edge whose source is in set 0. -/
def backward_preimage : KDerivation
    (imp bijectionFormula.encode (imp (member 1 3) (existsCode 7 preimage.encode))) := by
  have hproj : KDerivation (imp (witness 7).encode preimage.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let W := (witness 7).encode
    have hw : Context [W] W := .head [] _
    have hm : Context [W] (member 0 7) := Context.conjunctionLeft hw
    have hg : Context [W] (graphFormula 6 7 3).encode :=
      Context.conjunctionLeft (Context.conjunctionRight hw)
    exact Context.conjunctionIntro hm hg
  have hlift : KDerivation (imp (existsCode 7 (witness 7).encode)
      (existsCode 7 preimage.encode)) := existsCongr 7 hproj
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 1 3, bijectionFormula.encode]
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 1 3) := .head _ _
  have hw : Context Γ (existsCode 7 (witness 7).encode) := .mp hm (.mp hb (.closed backward_witness))
  exact .mp hw (.closed hlift)

theorem backward_witness_certificate : theoremCode (certificate backward_witness) =
    imp bijectionFormula.encode (imp (member 1 3) (existsCode 7 (witness 7).encode)) :=
  certificate_correct backward_witness

theorem backward_preimage_certificate : theoremCode (certificate backward_preimage) =
    imp bijectionFormula.encode (imp (member 1 3) (existsCode 7 preimage.encode)) :=
  certificate_correct backward_preimage

end PASoundness.PAtoCompactBijectionBackwardAtThree

#print axioms PASoundness.PAtoCompactBijectionBackwardAtThree.backward_witness
#print axioms PASoundness.PAtoCompactBijectionBackwardAtThree.backward_preimage
#print axioms PASoundness.PAtoCompactBijectionBackwardAtThree.backward_witness_certificate
#print axioms PASoundness.PAtoCompactBijectionBackwardAtThree.backward_preimage_certificate
