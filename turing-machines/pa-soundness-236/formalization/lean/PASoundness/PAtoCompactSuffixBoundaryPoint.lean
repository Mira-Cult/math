import PASoundness.PAtoCompactFilterInstantiation
import PASoundness.PAtoCompactSegmentOrderPoint

/-! Pointwise suffix transfer along two edges of a supplied order isomorphism.
The whole-domain order, both actual suffix filters, both edges and all four
outer-membership guards are explicit. This constructs no graph or cut and
proves no quantified coverage, addition output transport, or PA theorem. The
fixed numbers are syntactic names; the objects denoted may coincide. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuffixBoundaryPoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSegmentOrderPoint
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Suffix 40 is the part of outer source 0 outside cut 2. -/
def sourceFilter : Nat := filterGraph 0 40 42 (neg (member 2 42))
/-- Suffix 41 is the part of outer target 1 outside cut 5. -/
def targetFilter : Nat := filterGraph 1 41 43 (neg (member 5 43))

private def source_filter_at : KDerivation
    (imp sourceFilter (both (imp (member 40 7) (both (member 0 7) (neg (member 2 7))))
      (imp (both (member 0 7) (neg (member 2 7))) (member 40 7)))) := by
  let P : Formula := (Formula.member 2 42).not
  have h := filter_at 0 40 42 7 P (by decide) (by decide) (by decide)
    (by decide) (by decide)
  simpa [P, sourceFilter, Formula.not, Formula.encode, replace, rename, neg] using h

private def target_filter_at : KDerivation
    (imp targetFilter (both (imp (member 41 3) (both (member 1 3) (neg (member 5 3))))
      (imp (both (member 1 3) (neg (member 5 3))) (member 41 3)))) := by
  let P : Formula := (Formula.member 5 43).not
  have h := filter_at 1 41 43 3 P (by decide) (by decide) (by decide)
    (by decide) (by decide)
  simpa [P, targetFilter, Formula.not, Formula.encode, replace, rename, neg] using h

/-- For the supplied graph6 edges 7→3 and 2→5, suffix membership at 7 and 3
is equivalent under both exact filters and the four outer-domain guards.
No equality or inequality of the denoted values is assumed. -/
def suffix_boundary_point : KDerivation
    (imp orderFormula.encode (imp sourceFilter (imp targetFilter
      (imp (member 0 7) (imp (member 0 2) (imp (member 1 3) (imp (member 1 5)
        (imp (graphFormula 6 7 3).encode (imp (graphFormula 6 2 5).encode
          (both (imp (member 40 7) (member 41 3))
            (imp (member 41 3) (member 40 7)))))))))))) := by
  let O := orderFormula.encode
  let F := sourceFilter
  let G := targetFilter
  let A := member 0 7
  let B := member 0 2
  let C := member 1 3
  let D := member 1 5
  let E := (graphFormula 6 7 3).encode
  let H := (graphFormula 6 2 5).encode
  let L := member 2 7
  let R := member 5 3
  let S := member 40 7
  let T := member 41 3
  let Γ := [H,E,D,C,B,A,G,F,O]
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
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hh : Context Γ H := .head _ _
  have hs : Context Γ (both (imp S (both A (neg L))) (imp (both A (neg L)) S)) :=
    .mp hf (.closed source_filter_at)
  have ht : Context Γ (both (imp T (both C (neg R))) (imp (both C (neg R)) T)) :=
    .mp hg (.closed target_filter_at)
  have hor : Context Γ (both (imp L R) (imp R L)) :=
    .mp hh (.mp he (.mp hd (.mp hc (.mp hb (.mp ha (.mp ho (.closed guarded_segment_order)))))))
  have hforward : Context Γ (imp S T) := by
    apply Context.deduction
    let Δ := S :: Γ
    have hS : Context Δ S := .head _ _
    have hsource : Context Δ (both A (neg L)) :=
      .mp hS (Context.conjunctionLeft (Context.under hs S))
    have hnL : Context Δ (neg L) := Context.conjunctionRight hsource
    have hnR : Context Δ (neg R) := by
      apply Context.deduction
      have hR : Context (R :: Δ) R := .head _ _
      have hRL : Context (R :: Δ) (imp R L) :=
        Context.conjunctionRight (Context.under (Context.under hor S) R)
      exact .mp (.mp hR hRL) (Context.under hnL R)
    have hC : Context Δ C := Context.under hc S
    exact .mp (Context.conjunctionIntro hC hnR)
      (Context.conjunctionRight (Context.under ht S))
  have hbackward : Context Γ (imp T S) := by
    apply Context.deduction
    let Δ := T :: Γ
    have hT : Context Δ T := .head _ _
    have htarget : Context Δ (both C (neg R)) :=
      .mp hT (Context.conjunctionLeft (Context.under ht T))
    have hnR : Context Δ (neg R) := Context.conjunctionRight htarget
    have hnL : Context Δ (neg L) := by
      apply Context.deduction
      have hL : Context (L :: Δ) L := .head _ _
      have hLR : Context (L :: Δ) (imp L R) :=
        Context.conjunctionLeft (Context.under (Context.under hor T) L)
      exact .mp (.mp hL hLR) (Context.under hnR L)
    have hA : Context Δ A := Context.under ha T
    exact .mp (Context.conjunctionIntro hA hnL)
      (Context.conjunctionRight (Context.under hs T))
  exact Context.conjunctionIntro hforward hbackward

theorem suffix_boundary_point_certificate : theoremCode (certificate suffix_boundary_point) =
    imp orderFormula.encode (imp sourceFilter (imp targetFilter
      (imp (member 0 7) (imp (member 0 2) (imp (member 1 3) (imp (member 1 5)
        (imp (graphFormula 6 7 3).encode (imp (graphFormula 6 2 5).encode
          (both (imp (member 40 7) (member 41 3))
            (imp (member 41 3) (member 40 7))))))))))) :=
  certificate_correct suffix_boundary_point

end PASoundness.PAtoCompactSuffixBoundaryPoint

#print axioms PASoundness.PAtoCompactSuffixBoundaryPoint.sourceFilter
#print axioms PASoundness.PAtoCompactSuffixBoundaryPoint.targetFilter
#print axioms PASoundness.PAtoCompactSuffixBoundaryPoint.suffix_boundary_point
#print axioms PASoundness.PAtoCompactSuffixBoundaryPoint.suffix_boundary_point_certificate
