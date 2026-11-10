import PASoundness.PAtoCompactPartialInverseOutsidePredicate
import PASoundness.PAtoCompactOrderIsomorphism

/-! Join the outside-source branch with a supplied inside-source derivation
while retaining the actual forward bijection as an object-level antecedent.
This does not establish the inside branch, induction, or inverse existence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseGuardedCaseJoin
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPartialInversePredicate
open PASoundness.PAtoCompactPartialInverseOutsidePredicate PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The pointwise successor step follows from a supplied inside-source proof,
retaining the exact old graph's bijection formula as a K antecedent. -/
def guarded_successor_of_inside
    (inside : KDerivation (imp bijectionFormula.encode (imp (successorCode 8 10 15)
      (imp (member 0 8)
        (imp (replace 30 8 predicate).encode (replace 30 10 predicate).encode))))) :
    KDerivation (imp bijectionFormula.encode (imp (successorCode 8 10 15)
      (imp (replace 30 8 predicate).encode (replace 30 10 predicate).encode))) := by
  let B := bijectionFormula.encode
  let S := successorCode 8 10 15
  let X := member 0 8
  let P := (replace 30 8 predicate).encode
  let Q := (replace 30 10 predicate).encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [P,S,B]
  have hp : Context Γ P := Context.head _ _
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hex : Context Γ (either X (neg X)) := .closed (CompactHilbertBasis.identity (neg X))
  apply Context.disjunctionElim hex
  · let Δ := [X,P,S,B]
    have hx : Context Δ X := Context.head _ _
    have hp' : Context Δ P := Context.under hp X
    have hs' : Context Δ S := Context.under hs X
    have hb' : Context Δ B := Context.under hb X
    exact .mp hp' (.mp hx (.mp hs' (.mp hb' (.closed inside))))
  · let Δ := [neg X,P,S,B]
    have hn : Context Δ (neg X) := Context.head _ _
    have hp' : Context Δ P := Context.under hp (neg X)
    have hs' : Context Δ S := Context.under hs (neg X)
    exact .mp hp' (.mp hn (.mp hs' (.closed outside_predicate_step)))

theorem guarded_successor_of_inside_certificate
    (inside : KDerivation (imp bijectionFormula.encode (imp (successorCode 8 10 15)
      (imp (member 0 8)
        (imp (replace 30 8 predicate).encode (replace 30 10 predicate).encode))))) :
    theoremCode (certificate (guarded_successor_of_inside inside)) =
      imp bijectionFormula.encode (imp (successorCode 8 10 15)
        (imp (replace 30 8 predicate).encode (replace 30 10 predicate).encode)) :=
  certificate_correct (guarded_successor_of_inside inside)

end PASoundness.PAtoCompactPartialInverseGuardedCaseJoin

#print axioms PASoundness.PAtoCompactPartialInverseGuardedCaseJoin.guarded_successor_of_inside
#print axioms PASoundness.PAtoCompactPartialInverseGuardedCaseJoin.guarded_successor_of_inside_certificate
