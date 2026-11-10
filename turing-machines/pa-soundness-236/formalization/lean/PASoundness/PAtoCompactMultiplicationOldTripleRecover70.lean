import PASoundness.PAtoCompactMultiplicationOldTripleRecover
import PASoundness.PAtoCompactFreeVacuity

/-! Old-coordinate triple recovery at competitor label 70. The row invariant
contains an inner binder named 5, so the recovery proof generalizes only the
query implication under K vacuity of the retained invariant and then
instantiates that implication at 70. It does not rename the invariant or
assume distinct pair representatives are equal. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationOldTripleRecover70
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFixedFirstCoverageBase PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactMultiplicationOldTripleIntro
open PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha
open PASoundness.PAtoCompactMultiplicationOldTripleRecover
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- A query at output 70 with old major 3 already belonged to the old graph,
under the supplied no-garbage invariant. Labels name syntax only. -/
def recover_old_triple_70 : KDerivation (imp (member 30 3)
    (imp (noGarbage 64).encode
      (imp (replace 5 70 queriedTriple).encode (replace 5 70 oldTriple).encode))) := by
  let M : Formula := .member 30 3
  let N := noGarbage 64
  let Q := Formula.imp queriedTriple oldTriple
  have hvM : KDerivation (imp M.encode (allCode 5 M.encode)) := M.vacuity 5 (by decide)
  have hvN : KDerivation (imp N.encode (allCode 5 N.encode)) := free_vacuity 5 N (by decide)
  let Γ := [N.encode,M.encode]
  have hn : Context Γ N.encode := .head _ _
  have hm : Context Γ M.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ Q.encode := .mp hn (.mp hm (.closed recover_old_triple))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 5 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases he : h = N.encode
    · subst h; exact hvN
    · have he' : h = M.encode := hh.resolve_left he
      subst h; exact hvM
  have hall : Context Γ (allCode 5 Q.encode) := Context.generalize 5 hv hp
  have hi := universalInstance 5 70 Q (by decide) (by decide) (by decide)
  have h : Context Γ (replace 5 70 Q).encode := .mp hall (.closed hi)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  simpa [Γ,M,N,Q,Formula.encode,replace] using h

theorem recover_old_triple_70_certificate :
    theoremCode (certificate recover_old_triple_70) =
      imp (member 30 3) (imp (noGarbage 64).encode
        (imp (replace 5 70 queriedTriple).encode (replace 5 70 oldTriple).encode)) :=
  certificate_correct recover_old_triple_70
end PASoundness.PAtoCompactMultiplicationOldTripleRecover70
#print axioms PASoundness.PAtoCompactMultiplicationOldTripleRecover70.recover_old_triple_70
#print axioms PASoundness.PAtoCompactMultiplicationOldTripleRecover70.recover_old_triple_70_certificate
