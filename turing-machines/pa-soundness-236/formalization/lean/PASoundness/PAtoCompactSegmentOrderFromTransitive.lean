import PASoundness.PAtoCompactSegmentRestrictedOrderAll
import PASoundness.PAtoCompactOuterDomain

/-! Order preservation on arbitrary member segments. The two outer objects
are transitive, both selected segments belong to them, and the endpoint filter
and original order matrix are supplied. This constructs no graph or quotient. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSegmentOrderFromTransitive
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactOuterDomain
open PASoundness.PAtoCompactSegmentRestrictedOrderPoint PASoundness.PAtoCompactSegmentRestrictedOrderAll
open PASoundness.PAtoCompactRestrictedOrderAll
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Under outer transitivity, selected member segments are subsets; the
filtered graph therefore preserves the original membership order on them. -/
def segment_order_from_transitive : KDerivation
    (imp (transitiveCode 0 11 12) (imp (member 0 2)
      (imp (transitiveCode 1 16 18) (imp (member 1 5)
        (imp orderFormula.encode (imp filter restrictedOrder)))))) := by
  let T0 := transitiveCode 0 11 12
  let M0 := member 0 2
  let T1 := transitiveCode 1 16 18
  let M1 := member 1 5
  let O := orderFormula.encode
  let F := filter
  let Γ := [F,O,M1,T1,M0,T0]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have ht0 : Context Γ T0 := .hypothesis (by simp [Γ])
  have hm0 : Context Γ M0 := .hypothesis (by simp [Γ])
  have ht1 : Context Γ T1 := .hypothesis (by simp [Γ])
  have hm1 : Context Γ M1 := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .head _ _
  have hs0 : Context Γ (subsetCode 2 0 9) := .mp hm0 (.mp ht0
    (.closed (transitive_member_subset 0 2 11 12 9 (by decide))))
  have hs1 : Context Γ (subsetCode 5 1 10) := .mp hm1 (.mp ht1
    (.closed (transitive_member_subset 1 5 16 18 10 (by decide))))
  exact .mp hf (.mp ho (.mp hs1 (.mp hs0 (.closed segment_restricted_order_all))))

theorem segment_order_from_transitive_certificate :
    theoremCode (certificate segment_order_from_transitive) =
      imp (transitiveCode 0 11 12) (imp (member 0 2)
        (imp (transitiveCode 1 16 18) (imp (member 1 5)
          (imp orderFormula.encode (imp filter restrictedOrder))))) :=
  certificate_correct segment_order_from_transitive

end PASoundness.PAtoCompactSegmentOrderFromTransitive

#print axioms PASoundness.PAtoCompactSegmentOrderFromTransitive.segment_order_from_transitive
#print axioms PASoundness.PAtoCompactSegmentOrderFromTransitive.segment_order_from_transitive_certificate
