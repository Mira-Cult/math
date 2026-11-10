import PASoundness.PAtoCompactSeededSpanCrossDisjoint
import PASoundness.PAtoCompactSeededSpanOrderSplit

/-! Pointwise source and target uniqueness for a seeded span, reducing the
same-kind cases to explicit K implications and discharging both mixed cases by
the proved clean-suffix separation. This is not totality or a full bijection. -/
namespace PASoundness.PAtoCompactSeededSpanPointUniqueness

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSeededSpanBase
open PASoundness.PAtoCompactSeededSpanOrderSplit PASoundness.PAtoCompactSeededSpanOrderCases
open PASoundness.PAtoCompactSeededSpanPointOrder PASoundness.PAtoCompactSeededSpanCrossDisjoint
open PASoundness.PAtoCompactFirstSpanPathOutside PASoundness.PAtoCompactFirstSpanTargetOutside

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- For two two-case edges, the mixed cases are impossible when the input
equality holds, and the two same-kind cases imply the requested equality. -/
private def case_unique (P R Q S E F : Nat) : KDerivation
    (imp (either P R) (imp (either Q S) (imp (imp P (imp Q (imp E F)))
      (imp (imp R (imp S (imp E F))) (imp (imp P (imp S (neg E)))
        (imp (imp R (imp Q (neg E))) (imp E F))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [E,imp R (imp Q (neg E)),imp P (imp S (neg E)),imp R (imp S (imp E F)),
    imp P (imp Q (imp E F)),either Q S,either P R]
  have hcase1 : Context Γ (either P R) := .hypothesis (by simp [Γ])
  have hcase2 : Context Γ (either Q S) := .hypothesis (by simp [Γ])
  apply Context.disjunctionElim hcase1
  · have hcase2' := Context.under hcase2 P
    apply Context.disjunctionElim hcase2'
    · let Δ := Q :: P :: Γ
      have hq : Context Δ Q := .head _ _
      have hp : Context Δ P := .hypothesis (by simp [Δ])
      have he : Context Δ E := .hypothesis (by simp [Δ,Γ])
      have hu : Context Δ (imp P (imp Q (imp E F))) := .hypothesis (by simp [Δ,Γ])
      exact .mp he (.mp hq (.mp hp hu))
    · let Δ := S :: P :: Γ
      have hs : Context Δ S := .head _ _
      have hp : Context Δ P := .hypothesis (by simp [Δ])
      have he : Context Δ E := .hypothesis (by simp [Δ,Γ])
      have hn : Context Δ (imp P (imp S (neg E))) := .hypothesis (by simp [Δ,Γ])
      exact Context.explode F (.mp he (.mp hs (.mp hp hn)))
  · have hcase2' := Context.under hcase2 R
    apply Context.disjunctionElim hcase2'
    · let Δ := Q :: R :: Γ
      have hq : Context Δ Q := .head _ _
      have hr : Context Δ R := .hypothesis (by simp [Δ])
      have he : Context Δ E := .hypothesis (by simp [Δ,Γ])
      have hn : Context Δ (imp R (imp Q (neg E))) := .hypothesis (by simp [Δ,Γ])
      exact Context.explode F (.mp he (.mp hq (.mp hr hn)))
    · let Δ := S :: R :: Γ
      have hs : Context Δ S := .head _ _
      have hr : Context Δ R := .hypothesis (by simp [Δ])
      have he : Context Δ E := .hypothesis (by simp [Δ,Γ])
      have hu : Context Δ (imp R (imp S (imp E F))) := .hypothesis (by simp [Δ,Γ])
      exact .mp he (.mp hs (.mp hr hu))

def seedSourceUnique : Nat := imp firstSeed (imp secondSeed (imp (equal 2 26) (equal 3 27)))
def pathSourceUnique : Nat := imp firstPath (imp secondPath (imp (equal 2 26) (equal 3 27)))
def seedTargetUnique : Nat := imp firstSeed (imp secondSeed (imp (equal 3 27) (equal 2 26)))
def pathTargetUnique : Nat := imp firstPath (imp secondPath (imp (equal 3 27) (equal 2 26)))
def pointUniqueness : Nat := both (imp (equal 2 26) (equal 3 27))
  (imp (equal 3 27) (equal 2 26))

private def assumptions : List Nat := [(graphFormula 9 26 27).encode,(graphFormula 9 2 3).encode,
  both (member 0 26) (member 8 27),both (member 0 2) (member 8 3),pathTargetUnique,
  seedTargetUnique,pathSourceUnique,seedSourceUnique,targetGuard.encode,outsideGuard.encode,
  seedEndpoints,seededSpan.encode]

/-- Both pointwise uniqueness directions follow from the actual seeded
invariant and edges, the displayed same-kind uniqueness inputs, and the
clean-suffix disjointness hypotheses. -/
private def point_unique_context : Context assumptions pointUniqueness := by
  let Γ := assumptions
  have he2 : Context Γ (graphFormula 9 26 27).encode := .head _ _
  have he1 : Context Γ (graphFormula 9 2 3).encode := .hypothesis (by simp [Γ,assumptions])
  have hd2 : Context Γ (both (member 0 26) (member 8 27)) := .hypothesis (by simp [Γ,assumptions])
  have hd1 : Context Γ (both (member 0 2) (member 8 3)) := .hypothesis (by simp [Γ,assumptions])
  have hpt : Context Γ pathTargetUnique := .hypothesis (by simp [Γ,assumptions])
  have hst : Context Γ seedTargetUnique := .hypothesis (by simp [Γ,assumptions])
  have hps : Context Γ pathSourceUnique := .hypothesis (by simp [Γ,assumptions])
  have hss : Context Γ seedSourceUnique := .hypothesis (by simp [Γ,assumptions])
  have ht : Context Γ targetGuard.encode := .hypothesis (by simp [Γ,assumptions])
  have hs : Context Γ outsideGuard.encode := .hypothesis (by simp [Γ,assumptions])
  have hend : Context Γ seedEndpoints := .hypothesis (by simp [Γ,assumptions])
  have hi : Context Γ seededSpan.encode := .hypothesis (by simp [Γ,assumptions])
  have hsplit1 : Context Γ (either firstSeed firstPath) := .mp he1 (.mp hd1 (.mp hi (.closed first_edge_split)))
  have hsplit2 : Context Γ (either secondSeed secondPath) := .mp he2 (.mp hd2 (.mp hi (.closed second_edge_split)))
  have hmixSF : Context Γ (imp firstSeed (imp secondPath (neg (equal 2 26)))) :=
    .mp hs (.mp hend (.closed seed_path_source_disjoint))
  have hmixSR : Context Γ (imp firstPath (imp secondSeed (neg (equal 2 26)))) :=
    .mp hs (.mp hend (.closed path_seed_source_disjoint))
  have hmixTF : Context Γ (imp firstSeed (imp secondPath (neg (equal 3 27)))) :=
    .mp ht (.mp hend (.closed seed_path_target_disjoint))
  have hmixTR : Context Γ (imp firstPath (imp secondSeed (neg (equal 3 27)))) :=
    .mp ht (.mp hend (.closed path_seed_target_disjoint))
  have hsource : Context Γ (imp (equal 2 26) (equal 3 27)) :=
    .mp hmixSR (.mp hmixSF (.mp hps (.mp hss (.mp hsplit2 (.mp hsplit1
      (.closed (case_unique firstSeed firstPath secondSeed secondPath (equal 2 26) (equal 3 27))))))))
  have htarget : Context Γ (imp (equal 3 27) (equal 2 26)) :=
    .mp hmixTR (.mp hmixTF (.mp hpt (.mp hst (.mp hsplit2 (.mp hsplit1
      (.closed (case_unique firstSeed firstPath secondSeed secondPath (equal 3 27) (equal 2 26))))))))
  exact Context.conjunctionIntro hsource htarget

def point_uniqueness : KDerivation (imp seededSpan.encode (imp seedEndpoints
    (imp outsideGuard.encode (imp targetGuard.encode (imp seedSourceUnique (imp pathSourceUnique
      (imp seedTargetUnique (imp pathTargetUnique (imp (both (member 0 2) (member 8 3))
        (imp (both (member 0 26) (member 8 27)) (imp (graphFormula 9 2 3).encode
          (imp (graphFormula 9 26 27).encode pointUniqueness)))))))))))) := by
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
  apply Context.deduction
  apply Context.deduction
  exact point_unique_context

end PASoundness.PAtoCompactSeededSpanPointUniqueness

#print axioms PASoundness.PAtoCompactSeededSpanPointUniqueness.seedSourceUnique
#print axioms PASoundness.PAtoCompactSeededSpanPointUniqueness.pathSourceUnique
#print axioms PASoundness.PAtoCompactSeededSpanPointUniqueness.seedTargetUnique
#print axioms PASoundness.PAtoCompactSeededSpanPointUniqueness.pathTargetUnique
#print axioms PASoundness.PAtoCompactSeededSpanPointUniqueness.pointUniqueness
#print axioms PASoundness.PAtoCompactSeededSpanPointUniqueness.point_uniqueness
