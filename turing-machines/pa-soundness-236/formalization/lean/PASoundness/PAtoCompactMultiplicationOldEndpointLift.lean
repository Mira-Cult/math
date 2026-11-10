import PASoundness.PAtoCompactTransitiveClosure
import PASoundness.PAtoCompactRawSuccBridge

/-! Membership transport for old multiplication endpoints into the successor
factor and the new result with an actual old-result cut. This is a finite K
proof from the displayed graph, candidate and cut assumptions; it does not
construct the cut, a product graph, or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationOldEndpointLift
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactRawSuccBridge
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Every displayed old factor member belongs to its explicitly supplied
successor. The test name 39 must be distinct from the queried point. -/
def old_factor_member (a : Nat) (ha : 39 ≠ a) : KDerivation
    (imp (successorCode 30 38 39) (imp (member 30 a) (member 38 a))) := by
  have h := successor_include 30 38 39 a (by decide) (by decide) ha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 30 a, successorCode 30 38 39]
  have hm : Context Γ (member 30 a) := .head _ _
  have hs : Context Γ (successorCode 30 38 39) := .hypothesis (by simp [Γ])
  exact .mp (Context.disjunctionRight hm) (.mp hs (.closed h))

/-- A member of the old result remains in a candidate new result when the
old result is equal to, or is a member of, the new result. This uses
transitivity of the whole new result and no extensionality. -/
def old_result_member (z : Nat) (hz : 55 ≠ z) : KDerivation
    (imp (domainAt 100 45).encode
      (imp (either (equal 32 45) (member 45 32))
        (imp (member 32 z) (member 45 z)))) := by
  have htrans : KDerivation (imp (domainAt 100 45).encode (transitiveCode 45 54 55)) := by
    have h := candidate_transitive_frame 100 50 45 (by decide) (by decide) (by decide)
    simpa [namedTransitive, transitiveBody, transitiveCode, Formula.encode] using h
  have hchain := transitive_chain 45 54 55 32 z (by decide) (by decide)
    (by decide) (by decide) (by decide) hz
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 32 z, either (equal 32 45) (member 45 32), (domainAt 100 45).encode]
  have hm : Context Γ (member 32 z) := .head _ _
  have hc : Context Γ (either (equal 32 45) (member 45 32)) := .hypothesis (by simp [Γ])
  have hd : Context Γ (domainAt 100 45).encode := .hypothesis (by simp [Γ])
  have ht : Context Γ (transitiveCode 45 54 55) := .mp hd (.closed htrans)
  apply Context.disjunctionElim hc
  · have he : Context (equal 32 45 :: Γ) (equal 32 45) := .head _ _
    exact .mp (.under hm _) (.mp he (.closed (memberLeftEquality 32 45 z)))
  · have he : Context (member 45 32 :: Γ) (member 45 32) := .head _ _
    exact .mp (.under hm _) (.mp he (.mp (.under ht _) (.closed hchain)))

theorem old_factor_member_certificate (a : Nat) (ha : 39 ≠ a) :
    theoremCode (certificate (old_factor_member a ha)) =
      imp (successorCode 30 38 39) (imp (member 30 a) (member 38 a)) := certificate_correct _

theorem old_result_member_certificate (z : Nat) (hz : 55 ≠ z) :
    theoremCode (certificate (old_result_member z hz)) =
      imp (domainAt 100 45).encode
        (imp (either (equal 32 45) (member 45 32)) (imp (member 32 z) (member 45 z))) :=
  certificate_correct _
end PASoundness.PAtoCompactMultiplicationOldEndpointLift
#print axioms PASoundness.PAtoCompactMultiplicationOldEndpointLift.old_factor_member
#print axioms PASoundness.PAtoCompactMultiplicationOldEndpointLift.old_result_member
#print axioms PASoundness.PAtoCompactMultiplicationOldEndpointLift.old_factor_member_certificate
#print axioms PASoundness.PAtoCompactMultiplicationOldEndpointLift.old_result_member_certificate
