import PASoundness.PAtoCompactRestrictedOrderInstance
import PASoundness.PAtoCompactRestrictionEdgeReverseClosed
import PASoundness.PAtoCompactRestrictionFresh19
import PASoundness.PAtoCompactGreatestDownward

/-! Pointwise order transfer to an endpoint-restricted graph. The outer subset
relations, order and actual filter remain supplied K hypotheses. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSegmentRestrictedOrderPoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactGreatestDownward PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactRestrictionFilterVacuity
open PASoundness.PAtoCompactRestrictedOrderInstance
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def filter : Nat := filterGraph 6 8 14 (edgePredicate 14 2 5).encode

/-- Given old-domain guards 30,31∈2 and 32,33∈5 and the two restricted
edges, the original order clause supplies both literal membership-order
implications. The subset relations and endpoint filter are explicit premises;
no graph existence or quotient is inferred. All displayed labels are fixed
syntactic names, while the denoted objects may coincide. -/
def segment_restricted_order_point : KDerivation
    (imp (subsetCode 2 0 9) (imp (subsetCode 5 1 10)
      (imp orderFormula.encode (imp filter
        (imp (member 2 30) (imp (member 2 31)
          (imp (member 5 32) (imp (member 5 33)
            (imp (graphFormula 8 30 32).encode (imp (graphFormula 8 31 33).encode
              (both (imp (member 31 30) (member 33 32))
                (imp (member 33 32) (member 31 30))))))))))))) := by
  let SX := subsetCode 2 0 9
  let SY := subsetCode 5 1 10
  let O := orderFormula.encode
  let F := filter
  let A := member 2 30
  let B := member 2 31
  let C := member 5 32
  let D := member 5 33
  let H := (graphFormula 8 30 32).encode
  let I := (graphFormula 8 31 33).encode
  let Γ := [I,H,D,C,B,A,F,O,SY,SX]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hsx : Context Γ SX := .hypothesis (by simp [Γ])
  have hsy : Context Γ SY := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hh : Context Γ H := .hypothesis (by simp [Γ])
  have hi : Context Γ I := .head _ _
  have hA : Context Γ (member 0 30) := .mp ha (.mp hsx (.closed (subset_instance 2 0 9 30 (by decide) (by decide) (by decide))))
  have hB : Context Γ (member 0 31) := .mp hb (.mp hsx (.closed (subset_instance 2 0 9 31 (by decide) (by decide) (by decide))))
  have hC : Context Γ (member 1 32) := .mp hc (.mp hsy (.closed (subset_instance 5 1 10 32 (by decide) (by decide) (by decide))))
  have hD : Context Γ (member 1 33) := .mp hd (.mp hsy (.closed (subset_instance 5 1 10 33 (by decide) (by decide) (by decide))))
  have hfresh : 19 ∉ (namedFilter 6 8 14 2 5).names := by decide
  have hG : Context Γ (graphFormula 6 30 32).encode :=
    .mp hh (.mp hf (.closed (PAtoCompactRestrictionEdgeReverseClosed.restricted_edge_source
      6 8 14 2 5 30 32 (by decide) (by decide) (by decide) hfresh)))
  have hH : Context Γ (graphFormula 6 31 33).encode :=
    .mp hi (.mp hf (.closed (PAtoCompactRestrictionEdgeReverseClosed.restricted_edge_source
      6 8 14 2 5 31 33 (by decide) (by decide) (by decide) hfresh)))
  exact .mp hH (.mp hG (.mp hD (.mp hC (.mp hB (.mp hA
    (.mp ho (.closed guarded_order_fresh)))))))

theorem segment_restricted_order_point_certificate : theoremCode (certificate segment_restricted_order_point) =
    imp (subsetCode 2 0 9) (imp (subsetCode 5 1 10)
      (imp orderFormula.encode (imp filter
        (imp (member 2 30) (imp (member 2 31)
          (imp (member 5 32) (imp (member 5 33)
            (imp (graphFormula 8 30 32).encode (imp (graphFormula 8 31 33).encode
              (both (imp (member 31 30) (member 33 32))
                (imp (member 33 32) (member 31 30)))))))))))) :=
  certificate_correct segment_restricted_order_point

end PASoundness.PAtoCompactSegmentRestrictedOrderPoint

#print axioms PASoundness.PAtoCompactSegmentRestrictedOrderPoint.segment_restricted_order_point
#print axioms PASoundness.PAtoCompactSegmentRestrictedOrderPoint.segment_restricted_order_point_certificate
