import PASoundness.PAtoCompactFixedFirstPreservedBase
import PASoundness.PAtoCompactUniformBase
import PASoundness.PAtoCompactDomainClassification

/-! The uniform zero-prefix base for the fixed-first row invariant. This
constructs a finite K proof from the existing zero-prefix witness, retaining
preservation, coverage and no-garbage for the same graph. It does not prove
row collection for nonempty prefixes or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstUniformZeroBase
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactDomainClassification PASoundness.PAtoCompactFixedFirstPreservedBase
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The existential graph predicate used by fixed-first row induction. -/
def rowPredicate : Formula := .ex 7 (rowInvariantPreserved 7)

private def initialBody : Formula := .imp (.all 12 (.imp (.member 0 12) .bottom)) rowPredicate

private def initial : KDerivation initialBody.encode := by
  change KDerivation (imp (zeroCode 0 12) (existsCode 7 (rowInvariantPreserved 7).encode))
  exact zero_preserved_exists

private theorem body_replaced : replace 0 205 initialBody =
    .imp (.all 12 (.imp (.member 205 12) .bottom)) (replace 0 205 rowPredicate) := by decide

private def at205 : KDerivation (imp (zeroCode 205 12) (replace 0 205 rowPredicate).encode) := by
  have h := universalInstance 0 205 initialBody (by decide) (by decide) (by decide)
  have ha : KDerivation (replace 0 205 initialBody).encode := .mp (.generalize 0 initial) h
  rw [body_replaced] at ha
  exact ha

/-- The displayed quantified zero base is a finite K theorem. -/
def uniform_base : KDerivation (uniformBaseCode 0 205 207 rowPredicate) := by
  apply KDerivation.generalize 205
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [zeroCode 205 207]
  have hz : Context Γ (zeroCode 205 207) := .head _ _
  have hz' : Context Γ (zeroCode 205 12) :=
    .mp hz (.closed (zero_test_rename 205 207 12 (by decide) (by decide) (by decide)))
  exact .mp hz' (.closed at205)

theorem uniform_base_certificate : theoremCode (certificate uniform_base) =
    uniformBaseCode 0 205 207 rowPredicate := certificate_correct uniform_base
end PASoundness.PAtoCompactFixedFirstUniformZeroBase
#print axioms PASoundness.PAtoCompactFixedFirstUniformZeroBase.uniform_base
#print axioms PASoundness.PAtoCompactFixedFirstUniformZeroBase.uniform_base_certificate
