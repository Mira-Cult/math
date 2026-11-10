import PASoundness.PAtoCompactFixedFirstCoverageBase
import PASoundness.PAtoCompactProductRowOutsideEquivalent
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.CompactQuantifiers

/-! The no-garbage clause of the fixed-first row invariant is preserved across
an outside-domain prefix successor. This is a finite K formula transport,
not a row-collection or multiplication-totality theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstOutsideNoGarbage
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactProductRowOutsideEquivalent
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def oldBody : Formula := .imp (.member 7 9) (namedEither (.member 10 9) rowWitness)
private def newBody : Formula := CompactNamed.replace 0 1 oldBody
private def N : Formula := (Formula.member 31 0).not
private def S : Formula := namedSuccessor 0 1 2
private theorem old_body : (noGarbage 7) = .all 9 oldBody := rfl
private theorem new_body : CompactNamed.replace 0 1 (noGarbage 7) = .all 9 newBody := by decide
private theorem witness_old : PAtoCompactMultiplicationRowPrefixTransport.rowWitness 0 = rowWitness := by decide
private theorem witness_new : PAtoCompactMultiplicationRowPrefixTransport.rowWitness 1 =
    CompactNamed.replace 0 1 rowWitness := by decide

/-- No-garbage is preserved for the same graph when the added prefix point is
outside the row domain. Existing graph entries and all existential nested-pair
witnesses remain unchanged. -/
def outside_no_garbage : KDerivation (imp (successorCode 0 1 2)
    (imp (neg (member 31 0)) (imp (noGarbage 7).encode
      (CompactNamed.replace 0 1 (noGarbage 7)).encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(noGarbage 7).encode,neg (member 31 0),successorCode 0 1 2]
  have ho : Context Γ (noGarbage 7).encode := .head _ _
  have hn : Context Γ (neg (member 31 0)) := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode 0 1 2) := .hypothesis (by simp [Γ])
  have old_at : Context Γ oldBody.encode := by
    have h := allSpecialize 9 oldBody (by decide)
    have hall : Context Γ (allCode 9 oldBody.encode) := by simpa [old_body,Formula.encode] using ho
    exact .mp hall (.closed h)
  have heq : Context Γ (both
      (imp rowWitness.encode (CompactNamed.replace 0 1 rowWitness).encode)
      (imp (CompactNamed.replace 0 1 rowWitness).encode rowWitness.encode)) := by
    have h := Context.mp hn (Context.mp hs (.closed outside_row_witness_equivalent))
    simpa only [witness_old,witness_new] using h
  have hpoint : Context Γ newBody.encode := by
    apply Context.deduction
    let Δ := [member 7 9,(noGarbage 7).encode,neg (member 31 0),successorCode 0 1 2]
    have hm : Context Δ (member 7 9) := .head _ _
    have hc : Context Δ (either (member 10 9) rowWitness.encode) := by
      have h := Context.under old_at (member 7 9)
      have h' : Context Δ (imp (member 7 9) (either (member 10 9) rowWitness.encode)) := by
        simpa [oldBody,Formula.encode,namedEither,Formula.not,neg,either] using h
      exact .mp hm h'
    have hr : Context Δ (imp rowWitness.encode (CompactNamed.replace 0 1 rowWitness).encode) :=
      Context.under (Context.conjunctionLeft heq) _
    change Context Δ (either (member 10 9) (CompactNamed.replace 0 1 rowWitness).encode)
    apply Context.disjunctionElim hc
    · exact Context.disjunctionLeft (.head _ _)
    · exact Context.disjunctionRight (.mp (.head _ _) (.under hr _))
  have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 9 q)) := by
    intro q hq
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hq
    by_cases h : q = (noGarbage 7).encode
    · subst q; exact free_vacuity 9 (noGarbage 7) (by decide)
    by_cases h' : q = neg (member 31 0)
    · subst q
      have hn' := N.vacuity 9 (by decide)
      simpa [N,Formula.not,Formula.encode,neg] using hn'
    · have he : q = successorCode 0 1 2 := by simpa [h,h'] using hq
      subst q
      have hs' := S.vacuity 9 (by decide)
      simpa [S,namedSuccessor,namedSuccessorBody,namedBoth,namedEither,Formula.encode,
        Formula.not,successorCode,both,neg,either] using hs'
  have hall := Context.generalize 9 hv hpoint
  simpa [new_body,Formula.encode] using hall

theorem outside_no_garbage_certificate : theoremCode (certificate outside_no_garbage) =
    imp (successorCode 0 1 2) (imp (neg (member 31 0))
      (imp (noGarbage 7).encode (CompactNamed.replace 0 1 (noGarbage 7)).encode)) :=
  certificate_correct outside_no_garbage
end PASoundness.PAtoCompactFixedFirstOutsideNoGarbage
#print axioms PASoundness.PAtoCompactFixedFirstOutsideNoGarbage.outside_no_garbage
#print axioms PASoundness.PAtoCompactFixedFirstOutsideNoGarbage.outside_no_garbage_certificate
