import PASoundness.PAtoCompactDiagonalInvariantBase
import PASoundness.PAtoCompactUniformBase

/-! A uniform zero-base derivation for the exact diagonal-graph predicate.
This is a K proof of the displayed base schema, not an induction theorem or a
claim that every candidate number already has a represented graph. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalUniformBase
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactDiagonalExistentialStep PASoundness.PAtoCompactDiagonalInvariantBase

/-- Predicate asserting a graph with coverage and no-garbage at input name 0. -/
def diagonalPredicate : Formula := .ex 11 (invariantNamed 0 11)

/-- The literal fixed-name base implication represented as named syntax. -/
def namedBase : Formula :=
  .imp (.all 12 (.imp (.member 0 12) .bottom)) diagonalPredicate

/-- Every displayed zero witness satisfies the named diagonal-graph predicate.
The name 34 avoids all the exact binders in both the zero test and predicate. -/
def uniform_diagonal_base : KDerivation (uniformBaseCode 0 34 12 diagonalPredicate) := by
  have hi := CompactNamed.universalInstance 0 34 namedBase (by decide) (by decide) (by decide)
  have hbase : namedBase.encode =
      imp (zeroCode 0 12) (existsCode 11 (invariantNamed 0 11).encode) := by rfl
  have hreplace : (CompactNamed.replace 0 34 namedBase).encode =
      imp (zeroCode 34 12) (CompactNamed.replace 0 34 diagonalPredicate).encode := by
    simp [namedBase, CompactNamed.replace, CompactNamed.rename, Formula.encode,
      zeroCode, CompactProof.neg]
  rw [hbase,hreplace] at hi
  have hpoint : KDerivation
      (imp (zeroCode 34 12) (CompactNamed.replace 0 34 diagonalPredicate).encode) :=
    .mp (.generalize 0 zero_diagonal_exists) hi
  exact .generalize 34 hpoint

theorem uniform_diagonal_base_certificate :
    theoremCode (certificate uniform_diagonal_base) = uniformBaseCode 0 34 12 diagonalPredicate :=
  certificate_correct uniform_diagonal_base

end PASoundness.PAtoCompactDiagonalUniformBase

#print axioms PASoundness.PAtoCompactDiagonalUniformBase.uniform_diagonal_base
#print axioms PASoundness.PAtoCompactDiagonalUniformBase.uniform_diagonal_base_certificate
