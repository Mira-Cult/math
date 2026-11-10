import PASoundness.PAtoCompactPartialCompositionOutsidePredicate
import PASoundness.PAtoCompactConditionalTransitivityEdgeForward

/-! Combine the outside-source branch with a supplied inside-source K proof,
retaining both actual input bijections as object-level antecedents. This
constructor does not prove the inside branch or graph collection. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionGuardedCaseJoin
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityEdgeForward
open PASoundness.PAtoCompactPartialCompositionPredicate PASoundness.PAtoCompactPartialCompositionOutsidePredicate
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The fixed-prefix successor step follows from a supplied inside-source
proof, with both graph-bijection formulas preserved as explicit hypotheses. -/
def guarded_successor_of_inside
    (inside : KDerivation (imp bijectionFormula.encode (imp secondBijection.encode
      (imp (successorCode 10 13 15) (imp (member 0 10)
        (imp (replace 30 10 predicate).encode (replace 30 13 predicate).encode)))))) :
    KDerivation (imp bijectionFormula.encode (imp secondBijection.encode
      (imp (successorCode 10 13 15)
        (imp (replace 30 10 predicate).encode (replace 30 13 predicate).encode)))) := by
  let B₁ := bijectionFormula.encode
  let B₂ := secondBijection.encode
  let S := successorCode 10 13 15
  let X := member 0 10
  let P := (replace 30 10 predicate).encode
  let Q := (replace 30 13 predicate).encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [P,S,B₂,B₁]
  have hp : Context Γ P := Context.head _ _
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hb₁ : Context Γ B₁ := .hypothesis (by simp [Γ])
  have hb₂ : Context Γ B₂ := .hypothesis (by simp [Γ])
  have hex : Context Γ (either X (neg X)) := .closed (CompactHilbertBasis.identity (neg X))
  apply Context.disjunctionElim hex
  · let Δ := [X,P,S,B₂,B₁]
    have hx : Context Δ X := Context.head _ _
    have hp' : Context Δ P := Context.under hp X
    have hs' : Context Δ S := Context.under hs X
    have hb₁' : Context Δ B₁ := Context.under hb₁ X
    have hb₂' : Context Δ B₂ := Context.under hb₂ X
    exact .mp hp' (.mp hx (.mp hs' (.mp hb₂' (.mp hb₁' (.closed inside)))))
  · let Δ := [neg X,P,S,B₂,B₁]
    have hn : Context Δ (neg X) := Context.head _ _
    have hp' : Context Δ P := Context.under hp (neg X)
    have hs' : Context Δ S := Context.under hs (neg X)
    exact .mp hp' (.mp hn (.mp hs' (.closed outside_predicate_step)))

theorem guarded_successor_of_inside_certificate
    (inside : KDerivation (imp bijectionFormula.encode (imp secondBijection.encode
      (imp (successorCode 10 13 15) (imp (member 0 10)
        (imp (replace 30 10 predicate).encode (replace 30 13 predicate).encode)))))) :
    theoremCode (certificate (guarded_successor_of_inside inside)) =
      imp bijectionFormula.encode (imp secondBijection.encode (imp (successorCode 10 13 15)
        (imp (replace 30 10 predicate).encode (replace 30 13 predicate).encode))) :=
  certificate_correct (guarded_successor_of_inside inside)

end PASoundness.PAtoCompactPartialCompositionGuardedCaseJoin

#print axioms PASoundness.PAtoCompactPartialCompositionGuardedCaseJoin.guarded_successor_of_inside
#print axioms PASoundness.PAtoCompactPartialCompositionGuardedCaseJoin.guarded_successor_of_inside_certificate
