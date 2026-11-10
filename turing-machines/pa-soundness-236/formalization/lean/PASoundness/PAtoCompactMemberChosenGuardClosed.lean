import PASoundness.PAtoCompactMemberChosenGuardInputs

/-! Instantiate the conditional same-graph cut/suffix collector under the
explicit original-graph guard. Original graph existence remains separate. -/
namespace PASoundness.PAtoCompactMemberChosenGuardClosed
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactMemberCutSelectedTarget PASoundness.PAtoCompactMemberChosenConditional
open PASoundness.PAtoCompactMemberChosenGuardInputs
set_option maxRecDepth 262144
set_option maxHeartbeats 0

/-- The actual guard names avoid the new suffix witness label. -/
theorem guard_names_38 : 38 ∉ guard.names := by decide
/-- The actual guard names avoid the new cut witness label. -/
theorem guard_names_41 : 41 ∉ guard.names := by decide

theorem guard_free_38 : 38 ∉ guard.free := by
  intro h
  exact guard_names_38 ((Formula.free_subset_names guard) h)

theorem guard_free_41 : 41 ∉ guard.free := by
  intro h
  exact guard_names_41 ((Formula.free_subset_names guard) h)

/-- Given the displayed explicit guard, K constructs a target cut/suffix pair
with both allocated equivalences, target membership and actual target suffix.
The original graph60 is shared by both input proofs; values may coincide. -/
noncomputable def chosen_from_guard : KDerivation (imp guard.encode chosen.encode) :=
  collect_selected guard guard_free_38 guard_free_41 guard_cut guard_suffix

theorem chosen_from_guard_certificate : theoremCode (certificate chosen_from_guard) =
    imp guard.encode chosen.encode := certificate_correct chosen_from_guard
end PASoundness.PAtoCompactMemberChosenGuardClosed

#print axioms PASoundness.PAtoCompactMemberChosenGuardClosed.chosen_from_guard
#print axioms PASoundness.PAtoCompactMemberChosenGuardClosed.chosen_from_guard_certificate
