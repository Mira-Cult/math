import PASoundness.PAtoCompactSuffixGuardedForwardUpgrade
import PASoundness.PAtoCompactFilterInstantiation

/-! Derive suffix containment from the actual relative-complement filter, then
use the common-source-guarded clean-graph forward upgrade. The suffix filter,
input forward clause and guarded graph-clean condition remain object-level K
antecedents. No graph/filter existence, candidate suffix or addition theorem
is asserted here. -/
namespace PASoundness.PAtoCompactSuffixFilterForwardUpgrade

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactCommonSourceSpanImages PASoundness.PAtoCompactSuffixGuardedForwardUpgrade

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def suffixPredicate : Formula := (Formula.member 33 35).not

def suffixFilter : Formula := .all 35 (namedFilterBody 0 31 35 suffixPredicate)

theorem suffix_filter_code : suffixFilter.encode =
    filterGraph 0 31 35 (neg (member 33 35)) := by rfl

/-- The literal relative-complement filter implies that every suffix member
belongs to the whole. No transitivity of the suffix is required. -/
def suffix_contained : KDerivation (imp suffixFilter.encode contained.encode) := by
  have hi := filter_at 0 31 35 4 suffixPredicate (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hi' : KDerivation (imp suffixFilter.encode
      (both (imp (member 31 4) (both (member 0 4) (neg (member 33 4))))
        (imp (both (member 0 4) (neg (member 33 4))) (member 31 4)))) := by
    simpa [suffix_filter_code, suffixPredicate, Formula.not, Formula.encode, replace, rename, neg] using hi
  let Γ := [suffixFilter.encode]
  have hf : Context Γ suffixFilter.encode := .head _ _
  have hpoint : Context Γ (imp (member 31 4) (member 0 4)) := by
    apply Context.deduction
    let Δ := [member 31 4,suffixFilter.encode]
    have hm : Context Δ (member 31 4) := .head _ _
    have hf' : Context Δ suffixFilter.encode := .under hf (member 31 4)
    have hfilter : Context Δ (both (imp (member 31 4) (both (member 0 4) (neg (member 33 4))))
        (imp (both (member 0 4) (neg (member 33 4))) (member 31 4))) :=
      .mp hf' (.closed hi')
    have hforward : Context Δ (imp (member 31 4) (both (member 0 4) (neg (member 33 4)))) :=
      Context.conjunctionLeft hfilter
    have hboth : Context Δ (both (member 0 4) (neg (member 33 4))) := .mp hm hforward
    exact Context.conjunctionLeft hboth
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 4 h)) := by
    intro h hh
    have he : h = suffixFilter.encode := by simpa [Γ] using hh
    subst h
    exact suffixFilter.vacuity 4 (by decide)
  have hall : Context Γ contained.encode := by
    simpa only [contained, Formula.encode] using Context.generalize 4 hv hpoint
  exact Context.closeEmpty (Context.deduction hall)

/-- A supplied suffix forward clause and guarded graph cleanliness imply the
whole-image forward clause under the actual relative-complement filter. -/
def forward_upgrade_from_filter : KDerivation (imp suffixForward.encode
    (imp suffixFilter.encode (imp graphClean.encode firstClause.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [graphClean.encode,suffixFilter.encode,suffixForward.encode]
  have hc : Context Γ graphClean.encode := .head _ _
  have hf : Context Γ suffixFilter.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ suffixForward.encode := .hypothesis (by simp [Γ])
  have hcontained : Context Γ contained.encode := .mp hf (.closed suffix_contained)
  exact .mp hc (.mp hcontained (.mp hs (.closed suffix_forward_upgrade)))

theorem forward_upgrade_from_filter_certificate :
    theoremCode (certificate forward_upgrade_from_filter) =
      imp suffixForward.encode (imp suffixFilter.encode (imp graphClean.encode firstClause.encode)) :=
  certificate_correct forward_upgrade_from_filter

end PASoundness.PAtoCompactSuffixFilterForwardUpgrade

#print axioms PASoundness.PAtoCompactSuffixFilterForwardUpgrade.suffixPredicate
#print axioms PASoundness.PAtoCompactSuffixFilterForwardUpgrade.suffixFilter
#print axioms PASoundness.PAtoCompactSuffixFilterForwardUpgrade.suffix_filter_code
#print axioms PASoundness.PAtoCompactSuffixFilterForwardUpgrade.suffix_contained
#print axioms PASoundness.PAtoCompactSuffixFilterForwardUpgrade.forward_upgrade_from_filter
#print axioms PASoundness.PAtoCompactSuffixFilterForwardUpgrade.forward_upgrade_from_filter_certificate
