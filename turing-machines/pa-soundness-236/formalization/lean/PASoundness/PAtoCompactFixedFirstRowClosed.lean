import PASoundness.PAtoCompactFixedFirstRowFromLocal
import PASoundness.PAtoCompactFixedFirstStepRebase

/-! Fixed-first row collection from a candidate source and a supplied
map-bijection. This instantiates the preceding conditional induction with the
actual K local successor derivation. The row invariant does not itself require
mapping edges to land in the target. Downstream multiplication needs an
additional argument for target bounds and uniqueness. This does not prove multiplication
or the PA bridge. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstRowClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactFixedFirstRestrictedInduction
open PASoundness.PAtoCompactFixedFirstRowFromLocal
open PASoundness.PAtoCompactFixedFirstStepRebase
open PASoundness.PAtoCompactMultiplicationRowMapEdge

/-- A candidate source and the supplied map-bijection entail the full-prefix
fixed-first row invariant. No local successor proof is an input. -/
def row_exists : KDerivation
    (imp (candidateCode 31 213 209 210 202 0 203 205 206)
      (imp mapBijection.encode (replace 0 31 predicate).encode)) := by
  apply row_from_local
  exact local_successor_204

theorem row_exists_certificate : theoremCode (certificate row_exists) =
    imp (candidateCode 31 213 209 210 202 0 203 205 206)
      (imp mapBijection.encode (replace 0 31 predicate).encode) :=
  certificate_correct row_exists
end PASoundness.PAtoCompactFixedFirstRowClosed
#print axioms PASoundness.PAtoCompactFixedFirstRowClosed.row_exists
#print axioms PASoundness.PAtoCompactFixedFirstRowClosed.row_exists_certificate
