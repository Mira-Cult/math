import PASoundness.PAtoCompactFixedFirstRestrictedInduction
import PASoundness.PAtoCompactFixedFirstUniformZeroBase

/-! Candidate-restricted induction for fixed-first row collection, with the
zero-prefix base supplied as an actual finite K derivation. The displayed
candidate-restricted successor schema remains an explicit antecedent. This
is not a proof of nonempty row collection or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstInductionZeroClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactFixedFirstRestrictedInduction
open PASoundness.PAtoCompactFixedFirstUniformZeroBase
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- For candidate source 31, the full-prefix row invariant follows from the
explicit candidate-restricted step schema; the zero base is already proved. -/
def row_from_restricted_step : KDerivation
    (imp (candidateCode 31 213 209 210 202 0 203 205 206)
      (imp (allCode 201 (imp (candidateCode 201 213 209 210 202 0 203 205 206)
        (allStepsCode 201 0 204 205 208 209 210 predicate)))
        (replace 0 31 predicate).encode)) := by
  have hbase : KDerivation (uniformBaseCode 0 205 207 predicate) := by
    change KDerivation (uniformBaseCode 0 205 207 rowPredicate)
    exact uniform_base
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [allCode 201 (imp (candidateCode 201 213 209 210 202 0 203 205 206)
      (allStepsCode 201 0 204 205 208 209 210 predicate)),
    candidateCode 31 213 209 210 202 0 203 205 206]
  have hs : Context Γ (allCode 201 (imp (candidateCode 201 213 209 210 202 0 203 205 206)
      (allStepsCode 201 0 204 205 208 209 210 predicate))) := .head _ _
  have hd : Context Γ (candidateCode 31 213 209 210 202 0 203 205 206) :=
    .hypothesis (by simp [Γ])
  exact .mp hs (.mp (.closed hbase) (.mp hd (.closed fixed_induction)))

theorem row_from_restricted_step_certificate :
    theoremCode (certificate row_from_restricted_step) =
      imp (candidateCode 31 213 209 210 202 0 203 205 206)
        (imp (allCode 201 (imp (candidateCode 201 213 209 210 202 0 203 205 206)
          (allStepsCode 201 0 204 205 208 209 210 predicate)))
          (replace 0 31 predicate).encode) := certificate_correct row_from_restricted_step
end PASoundness.PAtoCompactFixedFirstInductionZeroClosed
#print axioms PASoundness.PAtoCompactFixedFirstInductionZeroClosed.row_from_restricted_step
#print axioms PASoundness.PAtoCompactFixedFirstInductionZeroClosed.row_from_restricted_step_certificate
