import PASoundness.PAtoCompactGraphRestriction

/-! An explicit named-syntax vacuity proof for a graph restriction filter.
This supplies one of the K proof-data hypotheses of edge elimination. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictionFilterVacuity
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactGraphRestriction
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Named copy of the exact filter graph, with its selector predicate kept
as syntax rather than replaced by a semantic relation. -/
def namedFilter (g h t x y : Nat) : Formula :=
  let P := edgePredicate t x y
  .all t (namedBoth
    (.imp (.member h t) (namedBoth (.member g t) P))
    (.imp (namedBoth (.member g t) P) (.member h t)))

theorem named_filter_code (g h t x y : Nat) :
    (namedFilter g h t x y).encode = filterGraph g h t (edgePredicate t x y).encode := by
  simp [namedFilter, namedBoth, filterGraph, filterPredicate, Formula.encode,
    CompactProof.both, CompactProof.neg]

/-- Any name absent from the full named filter, including all binders,
has a finite K vacuity derivation for the exact encoded filter graph. -/
def restriction_filter_vacuity (g h t x y q : Nat)
    (fresh : q ∉ (namedFilter g h t x y).names) :
    KDerivation (imp (filterGraph g h t (edgePredicate t x y).encode)
      (allCode q (filterGraph g h t (edgePredicate t x y).encode))) := by
  simpa only [named_filter_code] using (namedFilter g h t x y).vacuity q fresh

theorem restriction_filter_vacuity_certificate (g h t x y q : Nat)
    (fresh : q ∉ (namedFilter g h t x y).names) :
    theoremCode (certificate (restriction_filter_vacuity g h t x y q fresh)) =
      imp (filterGraph g h t (edgePredicate t x y).encode)
        (allCode q (filterGraph g h t (edgePredicate t x y).encode)) :=
  certificate_correct (restriction_filter_vacuity g h t x y q fresh)

end PASoundness.PAtoCompactRestrictionFilterVacuity

#print axioms PASoundness.PAtoCompactRestrictionFilterVacuity.restriction_filter_vacuity
