import PASoundness.PAtoCompactMultiplicationResultCutSplit
import PASoundness.PAtoCompactMultiplicationCandidate

/-! Assemble the literal multiplication reverse clause from two explicit K
preimage case proofs. The clean graph, witnesses, and point cases are not
constructed by this module; all are retained in the common guard or proof-data
inputs. No semantic soundness or multiplication totality is used. -/
namespace PASoundness.PAtoCompactMultiplicationReverseClauseFromCases
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactMultiplicationResultCutSplit
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The precise reverse clause for first factor 38, second factor 31, result
45 and represented graph 64. -/
def rebasedReverse : Formula :=
  replace 6 64 (replace 2 45 (replace 1 31 (replace 0 38 reverseFormula)))

/-- The exact output-5 preimage/uniqueness witness inside that literal clause. -/
def reverseWitness5 : Formula :=
  match rebasedReverse with
  | .all _ (.imp _ witness) => witness
  | _ => .bottom

/-- Syntactic identity; the complete original reverse formula is retained. -/
theorem rebased_reverse_shape : rebasedReverse =
    .all 5 (.imp (.member 45 5) reverseWitness5) := by decide

/-- Given separate K preimage proofs for an old-output member and for a suffix
member, the literal suffix filter splits each new-result member and supplies
its preimage. The exact K vacuity of the guard at name 5 is an explicit input. -/
def reverse_clause_from_cases (H : Formula)
    (hH : KDerivation (imp H.encode (allCode 5 H.encode)))
    (hfilter : KDerivation (imp H.encode suffixFilter))
    (oldCase : KDerivation (imp H.encode (imp (member 32 5) reverseWitness5.encode)))
    (suffixCase : KDerivation (imp H.encode (imp (member 40 5) reverseWitness5.encode))) :
    KDerivation (imp H.encode rebasedReverse.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [H.encode]
  have hHctx : Context Γ H.encode := .head _ _
  have hpoint : Context Γ (imp (member 45 5) reverseWitness5.encode) := by
    apply Context.deduction
    let Δ := [member 45 5,H.encode]
    have hm : Context Δ (member 45 5) := .head _ _
    have hh : Context Δ H.encode := .under hHctx _
    have hf : Context Δ suffixFilter := .mp hh (.closed hfilter)
    have hs : Context Δ (either (member 32 5) (member 40 5)) :=
      .mp hm (.mp hf (.closed (result_member_split 5 (by decide))))
    apply Context.disjunctionElim hs
    · have hp : Context (member 32 5 :: Δ) (member 32 5) := .head _ _
      exact .mp hp (.mp (.under hh _) (.closed oldCase))
    · have hp : Context (member 40 5 :: Δ) (member 40 5) := .head _ _
      exact .mp hp (.mp (.under hh _) (.closed suffixCase))
  have hall : Context Γ (allCode 5 (imp (member 45 5) reverseWitness5.encode)) := by
    apply Context.generalize 5 _ hpoint
    intro q hq
    have he : q = H.encode := by simpa [Γ] using hq
    subst q
    exact hH
  have hshape := rebased_reverse_shape
  rw [hshape]
  simpa [Formula.encode] using hall

theorem reverse_clause_from_cases_certificate (H : Formula)
    (hH : KDerivation (imp H.encode (allCode 5 H.encode)))
    (hfilter : KDerivation (imp H.encode suffixFilter))
    (oldCase : KDerivation (imp H.encode (imp (member 32 5) reverseWitness5.encode)))
    (suffixCase : KDerivation (imp H.encode (imp (member 40 5) reverseWitness5.encode))) :
    theoremCode (certificate (reverse_clause_from_cases H hH hfilter oldCase suffixCase)) =
      imp H.encode rebasedReverse.encode := certificate_correct _
end PASoundness.PAtoCompactMultiplicationReverseClauseFromCases
#print axioms PASoundness.PAtoCompactMultiplicationReverseClauseFromCases.rebased_reverse_shape
#print axioms PASoundness.PAtoCompactMultiplicationReverseClauseFromCases.reverse_clause_from_cases
#print axioms PASoundness.PAtoCompactMultiplicationReverseClauseFromCases.reverse_clause_from_cases_certificate
