import PASoundness.PAtoCompactOldImageContainedAligned

/-! K pointwise initial-segment order comparison for a supplied old
isomorphism matrix. The two outer-domain guards and both graph edges are
explicit; no graph restriction or semantic soundness is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSegmentOrderPoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoInstance
open PASoundness.PAtoCompactOldImageContainedAligned
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def m7 : Formula := replace 2 7 orderMatrix
private def m2 : Formula := replace 4 2 m7
/-- For old isomorphism edge (7,3) and distinguished edge (2,5), membership
7∈2 is equivalent to 3∈5, under all four displayed outer-domain guards. -/
def guarded_segment_order : KDerivation
    (imp orderFormula.encode
      (imp (member 0 7) (imp (member 0 2)
        (imp (member 1 3) (imp (member 1 5)
          (imp (graphFormula 6 7 3).encode (imp (graphFormula 6 2 5).encode
            (both (imp (member 2 7) (member 5 3))
              (imp (member 5 3) (member 2 7)))))))))) := by
  let A := member 0 7
  let B := member 0 2
  let C := member 1 3
  let D := member 1 5
  let E := (graphFormula 6 7 3).encode
  let F := (graphFormula 6 2 5).encode
  let L := member 2 7
  let R := member 5 3
  let Guard := both A (both B (both C (both D (both E F))))
  let Matrix := imp Guard (both (imp L R) (imp R L))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [F,E,D,C,B,A,orderFormula.encode]
  have ho : Context Γ orderFormula.encode := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .head _ _
  have hm : Context Γ Matrix := by
    have hi : Context Γ m2.encode := .mp ho (.closed aligned_order_instance)
    change Context Γ Matrix at hi
    exact hi
  have hg : Context Γ Guard := Context.conjunctionIntro ha (Context.conjunctionIntro hb
    (Context.conjunctionIntro hc (Context.conjunctionIntro hd (Context.conjunctionIntro he hf))))
  exact .mp hg hm

theorem guarded_segment_order_certificate :
    theoremCode (certificate guarded_segment_order) =
      imp orderFormula.encode
        (imp (member 0 7) (imp (member 0 2)
          (imp (member 1 3) (imp (member 1 5)
            (imp (graphFormula 6 7 3).encode (imp (graphFormula 6 2 5).encode
              (both (imp (member 2 7) (member 5 3))
                (imp (member 5 3) (member 2 7))))))))) :=
  certificate_correct guarded_segment_order

end PASoundness.PAtoCompactSegmentOrderPoint

#print axioms PASoundness.PAtoCompactSegmentOrderPoint.guarded_segment_order
#print axioms PASoundness.PAtoCompactSegmentOrderPoint.guarded_segment_order_certificate
