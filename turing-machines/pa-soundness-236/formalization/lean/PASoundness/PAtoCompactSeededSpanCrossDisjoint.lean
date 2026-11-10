import PASoundness.PAtoCompactSecondSpanPathOutside
import PASoundness.PAtoCompactSecondSpanTargetOutside
import PASoundness.PAtoCompactSeededSpanPointOrder

/-! A seed edge and a suffix-path edge cannot share a source or target point.
The seed endpoint implications and the clean suffix/filter guard used for
each side remain explicit K antecedents. This is pointwise and does not prove
the same-kind uniqueness cases or a graph bijection. -/
namespace PASoundness.PAtoCompactSeededSpanCrossDisjoint

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSeededSpanPointOrder PASoundness.PAtoCompactSeededSpanOrderCases
open PASoundness.PAtoCompactFirstSpanPathOutside PASoundness.PAtoCompactSecondSpanPathOutside
open PASoundness.PAtoCompactFirstSpanTargetOutside PASoundness.PAtoCompactSecondSpanTargetOutside

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A first seed edge and second path have different source points. -/
def seed_path_source_disjoint : KDerivation (imp seedEndpoints (imp outsideGuard.encode
    (imp firstSeed (imp secondPath (neg (equal 2 26)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal 2 26,secondPath,firstSeed,outsideGuard.encode,seedEndpoints]
  have he : Context Γ (equal 2 26) := .head _ _
  have hp : Context Γ secondPath := .hypothesis (by simp [Γ])
  have hs : Context Γ firstSeed := .hypothesis (by simp [Γ])
  have hc : Context Γ outsideGuard.encode := .hypothesis (by simp [Γ])
  have hd : Context Γ seedEndpoints := .hypothesis (by simp [Γ])
  have hpairs : Context Γ (both (member 40 2) (member 41 3)) := .mp hs (Context.conjunctionLeft hd)
  have hm : Context Γ (member 40 2) := Context.conjunctionLeft hpairs
  have hm' : Context Γ (member 40 26) := .mp he (.mp hm (.closed (memberRightEquality 40 2 26)))
  have hn : Context Γ (neg (member 40 26)) := .mp hp (.mp hc (.closed second_path_source_outside))
  exact .mp hm' hn

/-- A first path and second seed edge have different source points. -/
def path_seed_source_disjoint : KDerivation (imp seedEndpoints (imp outsideGuard.encode
    (imp firstPath (imp secondSeed (neg (equal 2 26)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal 2 26,secondSeed,firstPath,outsideGuard.encode,seedEndpoints]
  have he : Context Γ (equal 2 26) := .head _ _
  have hs : Context Γ secondSeed := .hypothesis (by simp [Γ])
  have hp : Context Γ firstPath := .hypothesis (by simp [Γ])
  have hc : Context Γ outsideGuard.encode := .hypothesis (by simp [Γ])
  have hd : Context Γ seedEndpoints := .hypothesis (by simp [Γ])
  have hpairs : Context Γ (both (member 40 26) (member 41 27)) := .mp hs (Context.conjunctionRight hd)
  have hm : Context Γ (member 40 26) := Context.conjunctionLeft hpairs
  have hm' : Context Γ (member 40 2) := .mp (Context.eqSymm he)
    (.mp hm (.closed (memberRightEquality 40 26 2)))
  have hn : Context Γ (neg (member 40 2)) := .mp hp (.mp hc (.closed first_path_source_outside))
  exact .mp hm' hn

/-- A first seed edge and second path have different target points. -/
def seed_path_target_disjoint : KDerivation (imp seedEndpoints (imp targetGuard.encode
    (imp firstSeed (imp secondPath (neg (equal 3 27)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal 3 27,secondPath,firstSeed,targetGuard.encode,seedEndpoints]
  have he : Context Γ (equal 3 27) := .head _ _
  have hp : Context Γ secondPath := .hypothesis (by simp [Γ])
  have hs : Context Γ firstSeed := .hypothesis (by simp [Γ])
  have hc : Context Γ targetGuard.encode := .hypothesis (by simp [Γ])
  have hd : Context Γ seedEndpoints := .hypothesis (by simp [Γ])
  have hpairs : Context Γ (both (member 40 2) (member 41 3)) := .mp hs (Context.conjunctionLeft hd)
  have hm : Context Γ (member 41 3) := Context.conjunctionRight hpairs
  have hm' : Context Γ (member 41 27) := .mp he (.mp hm (.closed (memberRightEquality 41 3 27)))
  have hn : Context Γ (neg (member 41 27)) := .mp hp (.mp hc (.closed second_path_target_outside))
  exact .mp hm' hn

/-- A first path and second seed edge have different target points. -/
def path_seed_target_disjoint : KDerivation (imp seedEndpoints (imp targetGuard.encode
    (imp firstPath (imp secondSeed (neg (equal 3 27)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal 3 27,secondSeed,firstPath,targetGuard.encode,seedEndpoints]
  have he : Context Γ (equal 3 27) := .head _ _
  have hs : Context Γ secondSeed := .hypothesis (by simp [Γ])
  have hp : Context Γ firstPath := .hypothesis (by simp [Γ])
  have hc : Context Γ targetGuard.encode := .hypothesis (by simp [Γ])
  have hd : Context Γ seedEndpoints := .hypothesis (by simp [Γ])
  have hpairs : Context Γ (both (member 40 26) (member 41 27)) := .mp hs (Context.conjunctionRight hd)
  have hm : Context Γ (member 41 27) := Context.conjunctionRight hpairs
  have hm' : Context Γ (member 41 3) := .mp (Context.eqSymm he)
    (.mp hm (.closed (memberRightEquality 41 27 3)))
  have hn : Context Γ (neg (member 41 3)) := .mp hp (.mp hc (.closed first_path_target_outside))
  exact .mp hm' hn

theorem seed_path_source_disjoint_certificate : theoremCode (certificate seed_path_source_disjoint) =
    imp seedEndpoints (imp outsideGuard.encode (imp firstSeed (imp secondPath (neg (equal 2 26))))) :=
  certificate_correct seed_path_source_disjoint
theorem path_seed_source_disjoint_certificate : theoremCode (certificate path_seed_source_disjoint) =
    imp seedEndpoints (imp outsideGuard.encode (imp firstPath (imp secondSeed (neg (equal 2 26))))) :=
  certificate_correct path_seed_source_disjoint
theorem seed_path_target_disjoint_certificate : theoremCode (certificate seed_path_target_disjoint) =
    imp seedEndpoints (imp targetGuard.encode (imp firstSeed (imp secondPath (neg (equal 3 27))))) :=
  certificate_correct seed_path_target_disjoint
theorem path_seed_target_disjoint_certificate : theoremCode (certificate path_seed_target_disjoint) =
    imp seedEndpoints (imp targetGuard.encode (imp firstPath (imp secondSeed (neg (equal 3 27))))) :=
  certificate_correct path_seed_target_disjoint

end PASoundness.PAtoCompactSeededSpanCrossDisjoint

#print axioms PASoundness.PAtoCompactSeededSpanCrossDisjoint.seed_path_source_disjoint
#print axioms PASoundness.PAtoCompactSeededSpanCrossDisjoint.path_seed_source_disjoint
#print axioms PASoundness.PAtoCompactSeededSpanCrossDisjoint.seed_path_target_disjoint
#print axioms PASoundness.PAtoCompactSeededSpanCrossDisjoint.path_seed_target_disjoint
#print axioms PASoundness.PAtoCompactSeededSpanCrossDisjoint.seed_path_source_disjoint_certificate
#print axioms PASoundness.PAtoCompactSeededSpanCrossDisjoint.path_seed_source_disjoint_certificate
#print axioms PASoundness.PAtoCompactSeededSpanCrossDisjoint.seed_path_target_disjoint_certificate
#print axioms PASoundness.PAtoCompactSeededSpanCrossDisjoint.path_seed_target_disjoint_certificate
