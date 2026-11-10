import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactZeroSuccessor
import PASoundness.CompactQuantifiers

/-! Extract a fresh preimage witness from the actual backward-bijection
clause. Code 1 remains the literal compact formula `member 0 0`. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactBijectionBackwardPreimage
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Backward-bijection matrix for preimage `i` and target `j`; graph 6 and
source 0 are fixed, with the uniqueness test bound at name 4. -/
def witnessBody (i j : Nat) : Formula := namedBoth (.member 0 i)
  (namedBoth (graphFormula 6 i j)
    (.all 4 (.imp (namedBoth (.member 0 4) (graphFormula 6 4 j)) (.equal 4 i))))

private def backwardClause : Formula :=
  .all 3 (.imp (.member 1 3) (.ex 2 (witnessBody 2 3)))

/-- Given the literal bijection matrix and the fact that target 5 belongs to
codomain 1, K derives a fresh-name preimage witness 7 with the displayed
backward matrix. The input, output and graph labels are syntactically fixed;
their denoted objects may coincide. This does not construct the graph. -/
def backward_preimage : KDerivation (imp bijectionFormula.encode
    (imp (member 1 5) (existsCode 7 (witnessBody 7 5).encode))) := by
  have hp : KDerivation (imp bijectionFormula.encode backwardClause.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    have hb : Context [bijectionFormula.encode] bijectionFormula.encode := Context.head [] _
    change Context [bijectionFormula.encode] (both _ backwardClause.encode) at hb
    exact Context.conjunctionRight hb
  have hi : KDerivation (imp backwardClause.encode
      (imp (member 1 5) (existsCode 2 (witnessBody 2 5).encode))) := by
    let f : Formula := .imp (.member 1 3) (.ex 2 (witnessBody 2 3))
    have h := CompactNamed.universalInstance 3 5 f (by decide) (by decide) (by decide)
    have hs : CompactNamed.replace 3 5 f =
        .imp (.member 1 5) (.ex 2 (witnessBody 2 5)) := by decide
    simpa only [backwardClause, f, hs, Formula.encode] using h
  have halpha : KDerivation (imp (existsCode 2 (witnessBody 2 5).encode)
      (existsCode 7 (witnessBody 7 5).encode)) := by
    have h := (CompactNamed.existentialAlpha 2 7 (witnessBody 2 5)
      (by decide) (by decide) (by decide)).1
    have hs : CompactNamed.replace 2 7 (witnessBody 2 5) = witnessBody 7 5 := by decide
    simpa only [hs] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 1 5,bijectionFormula.encode]
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 1 5) := Context.head _ _
  have he2 : Context Γ (existsCode 2 (witnessBody 2 5).encode) :=
    .mp hm (.mp hb (.closed (compose hp hi)))
  exact .mp he2 (.closed halpha)

theorem backward_preimage_certificate :
    theoremCode (certificate backward_preimage) = imp bijectionFormula.encode
      (imp (member 1 5) (existsCode 7 (witnessBody 7 5).encode)) :=
  certificate_correct backward_preimage

end PASoundness.PAtoCompactBijectionBackwardPreimage

#print axioms PASoundness.PAtoCompactBijectionBackwardPreimage.backward_preimage
#print axioms PASoundness.PAtoCompactBijectionBackwardPreimage.backward_preimage_certificate
