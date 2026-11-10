import PASoundness.PAtoCompactAddBaseSyntax
import PASoundness.PAtoCompactLiteralCutAdditionDefinition

/-! Pure name-allocation syntax for the literal-cut addition relation. This
file asserts neither witness existence nor K derivability. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLiteralCutBaseSyntax
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactLiteralCutAdditionDefinition
open PASoundness.PAtoCompactMultiAlpha PASoundness.PAtoCompactGuardElimination
open PASoundness.PAtoCompactMapNamesCongr PASoundness.PAtoCompactEquivStepsSyntax
open PASoundness.PAtoCompactAddBaseSyntax

/-- Literal-cut addition allocated to the given base and three input labels. -/
def literalCutAt (b x y z : Nat) : Formula :=
  mapNames (threeMap b 30 31 32 x y z) (normalizeBottom literalCut)

/-- The literal-cut template uses only its three parameter labels and the
same private-name inventory as the existing addition template. -/
theorem literalCut_names_subset : (normalizeBottom literalCut).names ⊆
    insert 30 (insert 31 (insert 32 addOffsets.toFinset)) := by decide

/-- Moving the listed private labels transports the exact syntax, while
preserving all three parameters. Parameter labels may coincide. -/
theorem renameSteps_literalCutAt (b c x y z : Nat)
    (hdis : b + 39 < c + 2) (hx : x < b + 2) (hy : y < b + 2)
    (hz : z < b + 2) :
    renameSteps (addSteps b c) (literalCutAt b x y z) = literalCutAt c x y z := by
  rw [renameSteps_eq_map]
  unfold literalCutAt
  rw [mapNames_compose]
  apply mapNames_congr
  intro k hk
  have hsupport := literalCut_names_subset hk
  simp only [Finset.mem_insert, List.mem_toFinset] at hsupport
  rcases hsupport with rfl | rfl | rfl | hm
  · simpa only [Function.comp_apply, threeMap, if_true] using addSteps_fix b c x hx
  · simpa only [Function.comp_apply, threeMap, Nat.reduceEqDiff, if_true, if_false] using addSteps_fix b c y hy
  · simpa only [Function.comp_apply, threeMap, Nat.reduceEqDiff, if_true, if_false] using addSteps_fix b c z hz
  · have hk30 : k ≠ 30 := by simp [addOffsets] at hm; omega
    have hk31 : k ≠ 31 := by simp [addOffsets] at hm; omega
    have hk32 : k ≠ 32 := by simp [addOffsets] at hm; omega
    simpa only [Function.comp_apply, threeMap, hk30, hk31, hk32, if_false] using
      addSteps_hit b c k hm hdis
end PASoundness.PAtoCompactLiteralCutBaseSyntax
#print axioms PASoundness.PAtoCompactLiteralCutBaseSyntax.literalCut_names_subset
#print axioms PASoundness.PAtoCompactLiteralCutBaseSyntax.renameSteps_literalCutAt
