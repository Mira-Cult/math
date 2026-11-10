import PASoundness.PAtoCompactFirstSpanPathOutside

/-! The literal source suffix filter sends a whole point outside cut40 into
suffix31. Both whole membership and nonmembership of the cut remain explicit. -/
namespace PASoundness.PAtoCompactSourceSuffixMembership

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactFirstSpanPathOutside

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The filter's reverse implication gives the actual suffix membership. -/
def source_point_in_suffix : KDerivation (imp suffixFilter.encode
    (imp (member 0 2) (imp (neg (member 40 2)) (member 31 2)))) := by
  have hi := filter_at 0 31 35 2 suffixPredicate (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hcode : suffixFilter.encode = filterGraph 0 31 35 (neg (member 40 35)) := by rfl
  have hi' : KDerivation (imp suffixFilter.encode
      (both (imp (member 31 2) (both (member 0 2) (neg (member 40 2))))
        (imp (both (member 0 2) (neg (member 40 2))) (member 31 2)))) := by
    simpa [hcode,suffixPredicate,Formula.not,Formula.encode,replace,rename,neg] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [neg (member 40 2),member 0 2,suffixFilter.encode]
  have hn : Context Γ (neg (member 40 2)) := .head _ _
  have hm : Context Γ (member 0 2) := .hypothesis (by simp [Γ])
  have hf : Context Γ suffixFilter.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ (both (imp (member 31 2) (both (member 0 2) (neg (member 40 2))))
      (imp (both (member 0 2) (neg (member 40 2))) (member 31 2))) := .mp hf (.closed hi')
  exact .mp (Context.conjunctionIntro hm hn) (Context.conjunctionRight hb)

theorem source_point_in_suffix_certificate : theoremCode (certificate source_point_in_suffix) =
    imp suffixFilter.encode (imp (member 0 2) (imp (neg (member 40 2)) (member 31 2))) :=
  certificate_correct source_point_in_suffix

end PASoundness.PAtoCompactSourceSuffixMembership

#print axioms PASoundness.PAtoCompactSourceSuffixMembership.source_point_in_suffix
#print axioms PASoundness.PAtoCompactSourceSuffixMembership.source_point_in_suffix_certificate
