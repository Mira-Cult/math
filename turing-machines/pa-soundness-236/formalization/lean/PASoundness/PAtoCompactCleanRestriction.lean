import PASoundness.PAtoCompactCleanMatrixData
import PASoundness.PAtoCompactRestrictionPredicateAt19
import PASoundness.PAtoCompactRestrictionFresh19

/-! A supplied endpoint-filter graph is clean in the exact K syntax used by
the conditional successor-isomorphism proof. This is not graph existence or
a matrix-transfer theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCleanRestriction
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.PAtoCompactCleanMatrixData PASoundness.PAtoCompactRestrictionPredicateAt19
open PASoundness.PAtoCompactRestrictionFresh19 PASoundness.PAtoCompactRestrictionFilterVacuity

/-- The exact endpoint filter at graph 6 implies every member of graph 6
has a represented pair with endpoints in 0 and 1. -/
def filter_is_clean : KDerivation (imp filterCode cleanGraph) := by
  have hfresh : [10,6,17,0,1,19,20,21,22,25,26].Nodup := by decide
  have h19 := filter_fresh_19 10 6 17 0 1 hfresh
  have hv : KDerivation (imp filterCode (allCode 19 filterCode)) :=
    restriction_filter_vacuity 10 6 17 0 1 19 h19
  have hpoint : KDerivation (imp filterCode
      (imp (member 6 19) (edgePredicate 19 0 1).encode)) :=
    filter_member_predicate 10 6 17 0 1 hfresh
  apply Context.closeEmpty
  apply Context.deduction
  have hp := Context.mp (Context.head [] filterCode) (.closed hpoint)
  exact Context.generalize 19 (by
    intro h hh
    have he : h = filterCode := by simpa using hh
    subst h
    exact hv) hp

theorem filter_is_clean_certificate : theoremCode (certificate filter_is_clean) =
    imp filterCode cleanGraph := certificate_correct filter_is_clean

end PASoundness.PAtoCompactCleanRestriction

#print axioms PASoundness.PAtoCompactCleanRestriction.filter_is_clean
#print axioms PASoundness.PAtoCompactCleanRestriction.filter_is_clean_certificate
