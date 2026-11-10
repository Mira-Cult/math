import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactZeroSuccessor
import PASoundness.CompactQuantifiers

/-! Expose a fresh forward-bijection witness from the exact proposed
isomorphism matrix. Negation and existence retain their literal K encoding,
whose code 1 is `member 0 0`. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactBijectionForwardWitness
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Exact forward witness body of `bijectionFormula`; input 2, selected
output 3, target set 1, graph 6 and competing-output binder 4. -/
def witness3 : Formula := namedBoth (.member 1 3) (namedBoth (graphFormula 6 2 3)
  (.all 4 (.imp (namedBoth (.member 1 4) (graphFormula 6 2 4)) (.equal 4 3))))

/-- The same matrix after capture-safe alpha-renaming of the selected output
from 3 to the fresh name 8. The free graph, set and input names stay fixed. -/
def witness8 : Formula := namedBoth (.member 1 8) (namedBoth (graphFormula 6 2 8)
  (.all 4 (.imp (namedBoth (.member 1 4) (graphFormula 6 2 4)) (.equal 4 8))))

private def forwardClause : Formula := .all 2 (.imp (.member 0 2) (.ex 3 witness3))

/-- Project the exact first bijection clause, instantiate its input at name 2,
and alpha-rename its output binder to 8. The displayed names are syntactic
labels; the denoted objects may coincide. This theorem neither creates the
graph nor asserts quotient laws. -/
def forward_witness : KDerivation (imp bijectionFormula.encode
    (imp (member 0 2) (existsCode 8 witness8.encode))) := by
  have hp : KDerivation (imp bijectionFormula.encode forwardClause.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    have hb : Context [bijectionFormula.encode] bijectionFormula.encode := Context.head [] _
    change Context [bijectionFormula.encode] (both forwardClause.encode _) at hb
    exact Context.conjunctionLeft hb
  have hi : KDerivation (imp forwardClause.encode
      (imp (member 0 2) (existsCode 3 witness3.encode))) := by
    let f : Formula := .imp (.member 0 2) (.ex 3 witness3)
    have h := CompactNamed.allSpecialize 2 f (by decide)
    simpa only [forwardClause, f, Formula.encode] using h
  have halpha : KDerivation (imp (existsCode 3 witness3.encode) (existsCode 8 witness8.encode)) := by
    have h := (CompactNamed.existentialAlpha 3 8 witness3 (by decide) (by decide) (by decide)).1
    have hs : CompactNamed.replace 3 8 witness3 = witness8 := by decide
    simpa only [hs] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 0 2, bijectionFormula.encode]
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 0 2) := Context.head _ _
  have he3 : Context Γ (existsCode 3 witness3.encode) := .mp hm (.mp hb (.closed (compose hp hi)))
  exact .mp he3 (.closed halpha)

theorem forward_witness_certificate :
    theoremCode (certificate forward_witness) =
      imp bijectionFormula.encode (imp (member 0 2) (existsCode 8 witness8.encode)) :=
  certificate_correct forward_witness

end PASoundness.PAtoCompactBijectionForwardWitness

#print axioms PASoundness.PAtoCompactBijectionForwardWitness.forward_witness
#print axioms PASoundness.PAtoCompactBijectionForwardWitness.forward_witness_certificate
