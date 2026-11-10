import PASoundness.PAtoCompactSuccRightOldCase
import PASoundness.PAtoCompactAdditionOldTargetWitnessTransfer

/-! Extract the old-target preimage for the distinct-top addition graph.
The old bijection matrix and old-target membership are explicit K premises.
This is not a graph extension, bijection of the new graph, or addition
 totality. All endpoint renamings are capture-checked. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionOldTargetFromBijection
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccRightOldCase
open PASoundness.PAtoCompactAdditionOldTargetWitnessTransfer
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The original supplied bijection/order matrix, with old source 31 and old
suffix 34. -/
def oldMatrixAt : Formula := replace 1 34 (replace 0 31 (namedBoth bijectionFormula orderFormula))

private def original : Formula := .imp (namedBoth bijectionFormula orderFormula)
  (.imp (.member 1 28) (oldWitness 28))

private def original_proof : KDerivation original.encode := by
  change KDerivation (imp oldMatrix (imp (member 1 28) (oldWitness 28).encode))
  exact old_target_witness

private def moved : Formula := replace 0 31 original
private def proof_at31 : KDerivation moved.encode := by
  have h := universalInstance 0 31 original (by decide) (by decide) (by decide)
  exact .mp (.generalize 0 original_proof) h

/-- For an old target 28 in the old suffix, the old matrix supplies the exact
preimage witness used by the addition witness-transfer theorem. -/
def old_target_from_matrix : KDerivation (imp oldMatrixAt.encode
    (imp (member 34 28) (Formula.ex 2 oldWitnessBody).encode)) := by
  have h := universalInstance 1 34 moved (by decide) (by decide) (by decide)
  have hc := KDerivation.mp (.generalize 1 proof_at31) h
  have hs : replace 1 34 moved = .imp oldMatrixAt
      (.imp (.member 34 28) (.ex 2 oldWitnessBody)) := by decide
  rw [hs] at hc
  exact hc

theorem old_target_from_matrix_certificate : theoremCode (certificate old_target_from_matrix) =
    imp oldMatrixAt.encode (imp (member 34 28) (Formula.ex 2 oldWitnessBody).encode) :=
  certificate_correct old_target_from_matrix
end PASoundness.PAtoCompactAdditionOldTargetFromBijection
#print axioms PASoundness.PAtoCompactAdditionOldTargetFromBijection.old_target_from_matrix
#print axioms PASoundness.PAtoCompactAdditionOldTargetFromBijection.old_target_from_matrix_certificate
