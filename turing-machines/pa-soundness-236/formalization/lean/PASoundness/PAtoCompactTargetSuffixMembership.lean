import PASoundness.PAtoCompactFirstSpanTargetOutside

/-! The literal target suffix filter sends a whole8 point outside cut41 into
suffix38. Both whole membership and nonmembership of the cut remain explicit. -/
namespace PASoundness.PAtoCompactTargetSuffixMembership

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactFirstSpanTargetOutside

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The filter's reverse implication gives actual suffix38 membership. -/
def target_point_in_suffix : KDerivation (imp targetFilter.encode
    (imp (member 8 3) (imp (neg (member 41 3)) (member 38 3)))) := by
  have hi := filter_at 8 38 35 3 targetPredicate (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hcode : targetFilter.encode = filterGraph 8 38 35 (neg (member 41 35)) := by rfl
  have hi' : KDerivation (imp targetFilter.encode
      (both (imp (member 38 3) (both (member 8 3) (neg (member 41 3))))
        (imp (both (member 8 3) (neg (member 41 3))) (member 38 3)))) := by
    simpa [hcode,targetPredicate,Formula.not,Formula.encode,replace,rename,neg] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [neg (member 41 3),member 8 3,targetFilter.encode]
  have hn : Context Γ (neg (member 41 3)) := .head _ _
  have hm : Context Γ (member 8 3) := .hypothesis (by simp [Γ])
  have hf : Context Γ targetFilter.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ (both (imp (member 38 3) (both (member 8 3) (neg (member 41 3))))
      (imp (both (member 8 3) (neg (member 41 3))) (member 38 3))) := .mp hf (.closed hi')
  exact .mp (Context.conjunctionIntro hm hn) (Context.conjunctionRight hb)

theorem target_point_in_suffix_certificate : theoremCode (certificate target_point_in_suffix) =
    imp targetFilter.encode (imp (member 8 3) (imp (neg (member 41 3)) (member 38 3))) :=
  certificate_correct target_point_in_suffix

end PASoundness.PAtoCompactTargetSuffixMembership

#print axioms PASoundness.PAtoCompactTargetSuffixMembership.target_point_in_suffix
#print axioms PASoundness.PAtoCompactTargetSuffixMembership.target_point_in_suffix_certificate
