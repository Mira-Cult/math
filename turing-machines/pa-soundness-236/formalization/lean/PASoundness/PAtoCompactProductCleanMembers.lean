import PASoundness.PAtoCompactProductCleanFilter

/-! The exact product filter implies that every retained graph member is a
nested pair with endpoints in the old input and result sets. This is a K
member-level cleanliness property, not yet preservation of each valid triple
or a multiplication isomorphism. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductCleanMembers
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactProductCleanFilter
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Literal K property of graph 54: each of its members has the displayed
nested-pair decomposition into endpoints from sets 0, 1, and 2. -/
def cleanCode : Nat := allCode 19 (imp (member 54 19) (cleanPredicate 19).encode)

private def namedFilter : Formula := .all 55 (namedFilterBody 6 54 55 (cleanPredicate 55))
private theorem namedFilter_code : namedFilter.encode = filterCode 54 := by rfl

/-- The filter antecedent does not mention graph witness name 19. -/
def filter_vacuity : KDerivation (imp (filterCode 54) (allCode 19 (filterCode 54))) := by
  have h := namedFilter.vacuity 19 (by decide)
  simpa only [namedFilter_code] using h

/-- A supplied exact product filter is clean, universally over its actual
members. -/
def filter_is_clean : KDerivation (imp (filterCode 54) cleanCode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [filterCode 54]
  have hf : Context Γ (filterCode 54) := .head _ _
  have hiff := Context.mp hf (.closed filter_at_graph_witness)
  have hlocal : Context Γ (imp (member 54 19) (cleanPredicate 19).encode) := by
    apply Context.deduction
    let Δ := member 54 19 :: Γ
    have hm : Context Δ (member 54 19) := .head _ _
    exact Context.conjunctionRight (.mp hm (.under (Context.conjunctionLeft hiff) _))
  exact Context.generalize 19 (by
    intro q hq
    have he : q = filterCode 54 := by simpa [Γ] using hq
    subst q
    exact filter_vacuity) hlocal

theorem filter_is_clean_certificate : theoremCode (certificate filter_is_clean) =
    imp (filterCode 54) cleanCode := certificate_correct filter_is_clean
end PASoundness.PAtoCompactProductCleanMembers
#print axioms PASoundness.PAtoCompactProductCleanMembers.filter_vacuity
#print axioms PASoundness.PAtoCompactProductCleanMembers.filter_is_clean
#print axioms PASoundness.PAtoCompactProductCleanMembers.filter_is_clean_certificate
