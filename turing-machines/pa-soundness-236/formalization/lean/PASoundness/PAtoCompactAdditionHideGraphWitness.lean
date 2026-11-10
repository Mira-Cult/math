import PASoundness.PAtoCompactAdditionSuccessorEquivStep

/-! Eliminate auxiliary pair and graph witnesses from an addition-successor
isomorphism witness while retaining the same suffix and its canonical quotient
equivalence. This does not establish existence, addition totality, or PA soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionHideGraphWitness
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactAdditionRightContext
open PASoundness.PAtoCompactAdditionSuccessorEquivStep
attribute [local irreducible] imp Cantor.pair Cantor.triangle
private def B := suffixWitness
private def P := pairF
private def G := graphA
private def Q := equivAt 38 40

private def remove_graph : KDerivation (imp (existsCode 9 (both G.encode Q.encode)) Q.encode) := by
  have hpoint : KDerivation (imp (both G.encode Q.encode) Q.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.conjunctionRight (.head _ _)
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.existsElim (Q.vacuity 9 (by decide)) (.closed (.generalize 9 hpoint)) (.head _ _)

private def remove_pair : KDerivation
    (imp (existsCode 11 (both P.encode (existsCode 9 (both G.encode Q.encode)))) Q.encode) := by
  have hpoint : KDerivation (imp (both P.encode (existsCode 9 (both G.encode Q.encode))) Q.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact .mp (Context.conjunctionRight (.head _ _)) (.closed remove_graph)
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.existsElim (Q.vacuity 11 (by decide)) (.closed (.generalize 11 hpoint)) (.head _ _)

/-- Any suffix with pair and graph witnesses satisfying the new equivalence
also witnesses the suffix condition and equivalence, with auxiliary pair and
graph names eliminated. The suffix at 40 is retained unchanged. -/
def hide_graph_witnesses : KDerivation
    (imp (existsCode 40 (both B.encode (existsCode 11 (both P.encode
      (existsCode 9 (both G.encode Q.encode))))))
      (existsCode 40 (both B.encode Q.encode))) := by
  have hpoint : KDerivation (imp (both B.encode (existsCode 11 (both P.encode
      (existsCode 9 (both G.encode Q.encode))))) (both B.encode Q.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [both B.encode (existsCode 11 (both P.encode (existsCode 9 (both G.encode Q.encode))))]
    have h : Context Γ _ := .head _ _
    exact Context.conjunctionIntro (Context.conjunctionLeft h)
      (.mp (Context.conjunctionRight h) (.closed remove_pair))
  exact existsCongr 40 hpoint

theorem hide_graph_witnesses_certificate : theoremCode (certificate hide_graph_witnesses) =
    imp (existsCode 40 (both B.encode (existsCode 11 (both P.encode
      (existsCode 9 (both G.encode Q.encode))))))
      (existsCode 40 (both B.encode Q.encode)) := certificate_correct hide_graph_witnesses
end PASoundness.PAtoCompactAdditionHideGraphWitness
#print axioms PASoundness.PAtoCompactAdditionHideGraphWitness.hide_graph_witnesses
#print axioms PASoundness.PAtoCompactAdditionHideGraphWitness.hide_graph_witnesses_certificate
