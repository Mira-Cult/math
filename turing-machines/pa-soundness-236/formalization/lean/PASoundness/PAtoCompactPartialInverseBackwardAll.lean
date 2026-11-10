import PASoundness.PAtoCompactPartialInverseBackwardPoint
import PASoundness.PAtoCompactPartialInverseCoverageAll

/-! Quantified backward coverage of a supplied partial-inverse successor step.
It uses the same explicit bundled premises as forward coverage; graph and
witness existence, successor induction and full interpretation remain open. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseBackwardAll
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactPartialInverseBase PASoundness.PAtoCompactPartialInverseInstantiate
open PASoundness.PAtoCompactPartialInverseCoverageAll PASoundness.PAtoCompactPartialInverseImageWitness
open PASoundness.PAtoCompactPartialInverseBackwardOld PASoundness.PAtoCompactPartialInverseBackwardPoint
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

/-- Every input/output pair in the two domains has backward coverage in the
new partial inverse graph. The direction is inverse edge to new-prefix and
forward edge. -/
def backwardFormula : Formula := .all 2 (.all 3
  (.imp (conj (.member 0 2) (.member 1 3))
    (.imp (graphFormula 9 3 2) (conj (.member 10 2) (graphFormula 6 2 3)))))

/-- From exactly the shared forward-coverage premises, derive all guarded
backward instances. The endpoint image, pair and adjunction remain supplied
inside that premise; no graph or witness existence is asserted. -/
def backward_all : KDerivation (imp suppliedPremises.encode backwardFormula.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let H := suppliedPremises.encode
  let Γ := [H]
  let Y := both (member 0 2) (member 1 3)
  let N := (graphFormula 9 3 2).encode
  have hlocal : Context Γ (imp Y (imp N newBackwardRhs)) := by
    apply Context.deduction
    apply Context.deduction
    let Δ := [N,Y,H]
    have hn : Context Δ N := Context.head _ _
    have hy : Context Δ Y := .hypothesis (by simp [Δ])
    have hh : Context Δ H := .hypothesis (by simp [Δ])
    have ha : Context Δ (adjoinCode 7 11 9 14) := Context.conjunctionLeft hh
    have ht₁ := Context.conjunctionRight hh
    have hp : Context Δ (pairFormula 11 13 12).encode := Context.conjunctionLeft ht₁
    have ht₂ := Context.conjunctionRight ht₁
    have hw : Context Δ imageWitness := Context.conjunctionLeft ht₂
    have hedge : Context Δ (graphFormula 6 12 13).encode :=
      Context.conjunctionLeft (Context.conjunctionRight hw)
    have ht₃ := Context.conjunctionRight ht₂
    have halias : Context Δ (equal 12 8) := Context.conjunctionLeft ht₃
    have ht₄ := Context.conjunctionRight ht₃
    have hs : Context Δ (successorCode 8 10 15) := Context.conjunctionLeft ht₄
    have hold : Context Δ partialInverse.encode := Context.conjunctionRight ht₄
    have hpoint : Context Δ pointFormula.encode := .mp hold (.closed partial_inverse_instance)
    rw [point_formula_code] at hpoint
    have hequiv : Context Δ (both
        (imp (graphFormula 7 3 2).encode
          (both (member 8 2) (graphFormula 6 2 3).encode))
        (imp (both (member 8 2) (graphFormula 6 2 3).encode)
          (graphFormula 7 3 2).encode)) := .mp hy hpoint
    have hback : Context Δ oldBackward := Context.conjunctionLeft hequiv
    exact .mp hn (.mp hedge (.mp halias (.mp hp (.mp ha (.mp hback (.mp hs (.closed backward_point)))))))
  have hv3 : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 3 q)) := by
    intro q hq
    have he : q = H := by simpa [Γ] using hq
    subst q
    exact premises_vacuity 3 fresh_3
  have hv2 : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 2 q)) := by
    intro q hq
    have he : q = H := by simpa [Γ] using hq
    subst q
    exact premises_vacuity 2 fresh_2
  exact Context.generalize 2 hv2 (Context.generalize 3 hv3 hlocal)

theorem backward_all_certificate : theoremCode (certificate backward_all) =
    imp suppliedPremises.encode backwardFormula.encode := certificate_correct backward_all

end PASoundness.PAtoCompactPartialInverseBackwardAll

#print axioms PASoundness.PAtoCompactPartialInverseBackwardAll.backward_all
#print axioms PASoundness.PAtoCompactPartialInverseBackwardAll.backward_all_certificate
