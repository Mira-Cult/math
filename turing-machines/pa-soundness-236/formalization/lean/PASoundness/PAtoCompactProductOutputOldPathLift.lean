import PASoundness.PAtoCompactProductOutputOutsidePathLift
import PASoundness.PAtoCompactTransitiveClosure

/-! Every old-prefix path remains a path in the successor prefix, preserving
its source output and payload. No source endpoint membership or graph
extension is inferred. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputOldPathLift

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactProductOutputOutsidePath PASoundness.PAtoCompactProductOutputOutsidePathLift
open PASoundness.PAtoCompactProductOutputPartialBase

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def successor : Formula := namedSuccessor 74 59 76

/-- The same selected source output remains in the successor prefix. -/
def old_body_lift : KDerivation (imp successor.encode (imp oldBody.encode nextBody.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldBody.encode,successor.encode]
  have hb : Context Γ oldBody.encode := .head _ _
  have hs : Context Γ successor.encode := .hypothesis (by simp [Γ])
  have hb' : Context Γ (both (member 74 32) payloadAt.encode) := by
    simpa [oldBody, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hb
  have hs' : Context Γ (successorCode 74 59 76) := by
    simpa [successor, namedSuccessor, namedSuccessorBody, successorCode, namedBoth, namedEither,
      CompactNamed.Formula.encode, both, neg, either] using hs
  have hd : Context Γ (either (equal 32 74) (member 74 32)) :=
    Context.disjunctionRight (Context.conjunctionLeft hb')
  have hm : Context Γ (member 59 32) :=
    .mp hd (.mp hs' (.closed (successor_include 74 59 76 32 (by decide) (by decide) (by decide))))
  simpa [nextBody, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
    Context.conjunctionIntro hm (Context.conjunctionRight hb')

def old_path_lift : KDerivation (imp (successorCode 74 59 76)
    (imp oldPath.encode pathAt.encode)) := by
  have h := conditionalExistsCongr 32 (successor.vacuity 32 (by decide)) old_body_lift
  have h' : KDerivation (imp (successorCode 74 59 76)
      (imp oldPath.encode nextPath.encode)) := by
    simpa [successor, namedSuccessor, namedSuccessorBody, successorCode, namedBoth, namedEither,
      oldPath, nextPath, CompactNamed.Formula.encode, both, neg, either] using h
  rw [next_path_shape] at h'
  exact h'

theorem old_path_lift_certificate : theoremCode (certificate old_path_lift) =
    imp (successorCode 74 59 76) (imp oldPath.encode pathAt.encode) := certificate_correct _

end PASoundness.PAtoCompactProductOutputOldPathLift

#print axioms PASoundness.PAtoCompactProductOutputOldPathLift.old_body_lift
#print axioms PASoundness.PAtoCompactProductOutputOldPathLift.old_path_lift
#print axioms PASoundness.PAtoCompactProductOutputOldPathLift.old_path_lift_certificate
