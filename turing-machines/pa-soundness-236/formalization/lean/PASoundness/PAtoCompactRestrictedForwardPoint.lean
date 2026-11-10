import PASoundness.PAtoCompactRestrictionEdgeEquivalence
import PASoundness.PAtoCompactTransitiveClosure
import PASoundness.PAtoCompactOldImageContainedAligned

/-! Pointwise edge transfer into an explicitly supplied restricted graph.
No graph existence, totality, quotient law, or PA interpretation is asserted.
Compact negation remains implication to literal code 1 (`member 0 0`). -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedForwardPoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactRestrictionEdgeEquivalence
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactOldImageContainedAligned
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The exact filter for old source name 2 and target name 5, applied to
supplied original graph 6 and restricted graph 8 with test name 14. -/
def filter : Nat := filterGraph 6 8 14 (edgePredicate 14 2 5).encode

/-- Given the exact endpoint filter, old-domain endpoints and an old edge,
K retains that edge in the restricted graph. The fixed numeric labels avoid
the internal pair and filter binders; the denoted objects may coincide. -/
def retain_old_point : KDerivation
    (imp filter (imp (member 2 7) (imp (member 5 3)
      (imp (graphFormula 6 7 3).encode (graphFormula 8 7 3).encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 7 3).encode,member 5 3,member 2 7,filter]
  have hg : Context Γ (graphFormula 6 7 3).encode := .head _ _
  have hy : Context Γ (member 5 3) := .hypothesis (by simp [Γ])
  have hx : Context Γ (member 2 7) := .hypothesis (by simp [Γ])
  have hf : Context Γ filter := .hypothesis (by simp [Γ])
  have hboth : Context Γ (both
      (imp (graphFormula 6 7 3).encode (graphFormula 8 7 3).encode)
      (imp (graphFormula 8 7 3).encode (graphFormula 6 7 3).encode)) := .mp hy (.mp hx (.mp hf (.closed
    (restricted_edge_iff 6 8 14 2 5 7 3 (by decide)))))
  exact .mp hg (Context.conjunctionLeft hboth)

theorem retain_old_point_certificate : theoremCode (certificate retain_old_point) =
    imp filter (imp (member 2 7) (imp (member 5 3)
      (imp (graphFormula 6 7 3).encode (graphFormula 8 7 3).encode))) :=
  certificate_correct retain_old_point

/-- For the supplied raw successor graphs and order clause, an old input 7
whose displayed original-graph image 3 lies in successor target 1 has that
image in old target 5. The exact endpoint filter then retains the edge. Both
successors, the order clause, the filter, top edge, and displayed old edge
remain explicit premises; no existential graph coverage is asserted. -/
def forward_old_point : KDerivation
    (imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp orderFormula.encode (imp filter
        (imp (graphFormula 6 2 5).encode (imp (member 2 7)
          (imp (member 1 3) (imp (graphFormula 6 7 3).encode
            (both (member 5 3) (graphFormula 8 7 3).encode))))))))) := by
  let SX := successorCode 2 0 9
  let SY := successorCode 5 1 10
  let O := orderFormula.encode
  let F := filter
  let T := (graphFormula 6 2 5).encode
  let I := member 2 7
  let J := member 1 3
  let E := (graphFormula 6 7 3).encode
  let Γ := [E,J,I,T,F,O,SY,SX]
  apply Context.closeEmpty
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
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hi : Context Γ I := .hypothesis (by simp [Γ])
  have hj : Context Γ J := .hypothesis (by simp [Γ])
  have he : Context Γ E := .head _ _
  have hsource : Context Γ (member 0 7) :=
    .mp (Context.disjunctionRight hi)
      (.mp hsx (.closed (successor_include 2 0 9 7 (by decide) (by decide) (by decide))))
  have hiff : Context Γ (both (imp (member 2 7) (member 5 3))
      (imp (member 5 3) (member 2 7))) :=
    .mp ht (.mp he (.mp hj (.mp hsource (.mp ho (.mp hsy (.mp hsx
      (.closed old_image_preimage_iff)))))))
  have htarget : Context Γ (member 5 3) := .mp hi (Context.conjunctionLeft hiff)
  have hnew : Context Γ (graphFormula 8 7 3).encode :=
    .mp he (.mp htarget (.mp hi (.mp hf (.closed retain_old_point))))
  exact Context.conjunctionIntro htarget hnew

theorem forward_old_point_certificate : theoremCode (certificate forward_old_point) =
    imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp orderFormula.encode (imp filter
        (imp (graphFormula 6 2 5).encode (imp (member 2 7)
          (imp (member 1 3) (imp (graphFormula 6 7 3).encode
            (both (member 5 3) (graphFormula 8 7 3).encode)))))))) :=
  certificate_correct forward_old_point

end PASoundness.PAtoCompactRestrictedForwardPoint

#print axioms PASoundness.PAtoCompactRestrictedForwardPoint.retain_old_point
#print axioms PASoundness.PAtoCompactRestrictedForwardPoint.retain_old_point_certificate
#print axioms PASoundness.PAtoCompactRestrictedForwardPoint.forward_old_point
#print axioms PASoundness.PAtoCompactRestrictedForwardPoint.forward_old_point_certificate
