import PASoundness.PAtoCompactCleanImageTransfer
import PASoundness.PAtoCompactDiagonalBijectionRight

/-! Exact left bijection-clause transfer between a supplied old graph and
its endpoint-restricted graph, under explicit guarded edge equivalence. This
is literal K proof data; no graph existence or quotient property is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCleanBijectionLeft
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCleanMatrixData PASoundness.PAtoCompactCleanImageWitness
open PASoundness.PAtoCompactCleanImageTransfer PASoundness.PAtoCompactDiagonalBijectionRight

/-- The exact left bijection clause for old graph name 10. -/
def oldLeft : Formula := replace 6 10 leftClause

theorem old_left_code : oldLeft.encode = oldImage := by rfl

theorem new_left_code : leftClause.encode = newImage := by rfl

/-- Guarded edge equivalence transfers the complete image clause, including
its unique-target quantifier, from old graph 10 to restricted graph 6. -/
def left_clause : KDerivation (imp guardedEdges.encode (imp oldLeft.encode leftClause.encode)) := by
  rw [old_left_code, new_left_code]
  exact transfer_image image_witness

theorem left_clause_certificate : theoremCode (certificate left_clause) =
    imp guardedEdges.encode (imp oldLeft.encode leftClause.encode) := certificate_correct left_clause

end PASoundness.PAtoCompactCleanBijectionLeft

#print axioms PASoundness.PAtoCompactCleanBijectionLeft.left_clause
#print axioms PASoundness.PAtoCompactCleanBijectionLeft.left_clause_certificate
