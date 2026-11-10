import PASoundness.PAtoCompactFixedFirstInductionZeroClosed
import PASoundness.PAtoCompactFixedFirstGuardedRestrictedStep

/-! Conditional fixed-first row collection under a candidate source and a
map-bijection. The relabeled local successor construction remains an explicit
finite K proof-data input. The invariant does not by itself rule out mapping
edges whose outputs lie outside the target; a separate cleanliness condition is
needed when using it for multiplication. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstRowFromLocal
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactFixedFirstRestrictedInduction
open PASoundness.PAtoCompactFixedFirstInductionZeroClosed
open PASoundness.PAtoCompactFixedFirstGuardedRestrictedStep
open PASoundness.PAtoCompactMultiplicationRowMapEdge
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A supplied relabeled local successor proof gives the full-prefix row
invariant from the literal candidate source and map-bijection assumptions. -/
def row_from_local (hlocal : KDerivation localCode) : KDerivation
    (imp (candidateCode 31 213 209 210 202 0 203 205 206)
      (imp mapBijection.encode (replace 0 31 predicate).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let C := candidateCode 31 213 209 210 202 0 203 205 206
  let M := mapBijection.encode
  let S := allCode 201 (imp (candidateCode 201 213 209 210 202 0 203 205 206)
    (allStepsCode 201 0 204 205 208 209 210 predicate))
  let Γ := [M,C]
  have hm : Context Γ M := .head _ _
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .mp hm (.closed (exact_step_of_local hlocal))
  exact .mp hs (.mp hc (.closed row_from_restricted_step))

theorem row_from_local_certificate (hlocal : KDerivation localCode) :
    theoremCode (certificate (row_from_local hlocal)) =
      imp (candidateCode 31 213 209 210 202 0 203 205 206)
        (imp mapBijection.encode (replace 0 31 predicate).encode) :=
  certificate_correct (row_from_local hlocal)
end PASoundness.PAtoCompactFixedFirstRowFromLocal
#print axioms PASoundness.PAtoCompactFixedFirstRowFromLocal.row_from_local
#print axioms PASoundness.PAtoCompactFixedFirstRowFromLocal.row_from_local_certificate
