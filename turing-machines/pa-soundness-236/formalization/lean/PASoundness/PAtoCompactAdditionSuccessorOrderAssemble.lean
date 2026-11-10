import PASoundness.PAtoCompactAdditionSuccessorEdgeSplitUnique
import PASoundness.PAtoCompactAdditionOrderComparisonTransport
import PASoundness.PAtoCompactAdditionSuccessorGraphClean
import PASoundness.PAtoCompactAdditionSuccessorGraphMixed
import PASoundness.PAtoCompactAdditionSuccessorGraphMixed45
import PASoundness.PAtoCompactAdditionSuccessorOldOld
import PASoundness.PAtoCompactSuccOrderPointShape

/-! Pointwise order preservation for an addition-successor graph extension.
The old source, whole result, suffix, old order and clean graph are explicit.
In particular, no transitivity of the suffix is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorOrderAssemble
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSuccOrderPointShape
open PASoundness.PAtoCompactAdditionSuccessorEdgeSplitUnique
open PASoundness.PAtoCompactAdditionOrderComparisonTransport
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private abbrev O := PASoundness.PAtoCompactAdditionSuccessorOldOld.oldOrder.encode
private abbrev C := PASoundness.PAtoCompactAdditionSuccessorGraphClean.oldClean.encode
private abbrev F := PASoundness.PAtoCompactAdditionSuccessorGraphClean.suffix
private abbrev S := PASoundness.PAtoCompactAdditionSuccessorGraphMixed.sourceTrans
private abbrev T := PASoundness.PAtoCompactAdditionSuccessorGraphMixed.targetTrans
private abbrev P := (pairFormula 11 31 32).encode
private abbrev A := adjoinCode 6 11 9 16
private abbrev G23 := (graphFormula 6 2 3).encode
private abbrev G45 := (graphFormula 6 4 5).encode
private abbrev T23 := both (equal 2 31) (equal 3 32)
private abbrev T45 := both (equal 4 31) (equal 5 32)
private abbrev H23 := (graphFormula 9 2 3).encode
private abbrev H45 := (graphFormula 9 4 5).encode
private abbrev context := [H45,H23,T,S,F,P,A,C,O]

/-- The two supplied new edges preserve order across the four combinations of
old and newly adjoined top edges. `S` and `T` are transitivity of the *whole*
old source and result; the relative target suffix need not be transitive. -/
def point_comparison : Context context comparison := by
  have hgraph : Context context A := .hypothesis (by simp [context])
  have hpair : Context context P := .hypothesis (by simp [context])
  have h23 : Context context H23 := .hypothesis (by simp [context])
  have h45 : Context context H45 := .head _ _
  have split23 : Context context (either G23 T23) :=
    .mp h23 (.mp hpair (.mp hgraph (.closed edge_split_23)))
  have split45 : Context context (either G45 T45) :=
    .mp h45 (.mp hpair (.mp hgraph (.closed edge_split_45)))
  apply Context.disjunctionElim split23
  · have split45' := Context.under split45 G23
    apply Context.disjunctionElim split45'
    · let Γ := G45 :: G23 :: context
      have ho : Context Γ O := .hypothesis (by simp [Γ,context])
      have hc : Context Γ C := .hypothesis (by simp [Γ,context])
      have hg23 : Context Γ G23 := .hypothesis (by simp [Γ,context])
      have hg45 : Context Γ G45 := .head _ _
      exact .mp hg45 (.mp hg23 (.mp hc (.mp ho (.closed PASoundness.PAtoCompactAdditionSuccessorOldOld.old_old_addition))))
    · let Γ := T45 :: G23 :: context
      have hc : Context Γ C := .hypothesis (by simp [Γ,context])
      have hf : Context Γ F := .hypothesis (by simp [Γ,context])
      have hg23 : Context Γ G23 := .hypothesis (by simp [Γ,context])
      have ht : Context Γ T45 := .head _ _
      have he : Context Γ PASoundness.PAtoCompactAdditionSuccessorGraphMixed.endpoints :=
        .mp hg23 (.mp hc (.closed (PASoundness.PAtoCompactAdditionSuccessorGraphClean.clean_endpoints 2 3 (by decide))))
      have hm : Context Γ PASoundness.PAtoCompactAdditionSuccessorGraphMixed.oldToTop :=
        .mp he (.mp hf (.closed PASoundness.PAtoCompactAdditionSuccessorGraphMixed.old_to_top))
      exact .mp hm (.mp ht (.closed old_top_transport))
  · have split45' := Context.under split45 T23
    apply Context.disjunctionElim split45'
    · let Γ := G45 :: T23 :: context
      have hc : Context Γ C := .hypothesis (by simp [Γ,context])
      have hf : Context Γ F := .hypothesis (by simp [Γ,context])
      have hs : Context Γ S := .hypothesis (by simp [Γ,context])
      have ht : Context Γ T := .hypothesis (by simp [Γ,context])
      have hg45 : Context Γ G45 := .head _ _
      have htop : Context Γ T23 := .hypothesis (by simp [Γ,context])
      have he : Context Γ PASoundness.PAtoCompactAdditionSuccessorGraphMixed45.endpoints :=
        .mp hg45 (.mp hc (.closed (PASoundness.PAtoCompactAdditionSuccessorGraphClean.clean_endpoints 4 5 (by decide))))
      have hm : Context Γ PASoundness.PAtoCompactAdditionSuccessorGraphMixed45.topToOld :=
        .mp he (.mp ht (.mp hs (.mp hf (.closed PASoundness.PAtoCompactAdditionSuccessorGraphMixed45.top_to_old))))
      exact .mp hm (.mp htop (.closed top_old_transport))
    · let Γ := T45 :: T23 :: context
      have h23 : Context Γ T23 := .hypothesis (by simp [Γ,context])
      have h45 : Context Γ T45 := .head _ _
      exact .mp (.closed PASoundness.PAtoCompactAdditionSuccessorGraphMixed45.top_to_top)
        (.mp h45 (.mp h23 (.closed top_top_transport)))

/-- Curried finite K proof certificate for the same pointwise comparison. -/
def point_comparison_closed : KDerivation (imp O (imp C (imp A (imp P (imp F
    (imp S (imp T (imp H23 (imp H45 comparison))))))))) := by
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
  exact point_comparison

theorem point_comparison_closed_certificate : theoremCode (certificate point_comparison_closed) =
    imp O (imp C (imp A (imp P (imp F (imp S (imp T (imp H23 (imp H45 comparison)))))))) :=
  certificate_correct point_comparison_closed
end PASoundness.PAtoCompactAdditionSuccessorOrderAssemble
#print axioms PASoundness.PAtoCompactAdditionSuccessorOrderAssemble.point_comparison_closed
#print axioms PASoundness.PAtoCompactAdditionSuccessorOrderAssemble.point_comparison_closed_certificate
