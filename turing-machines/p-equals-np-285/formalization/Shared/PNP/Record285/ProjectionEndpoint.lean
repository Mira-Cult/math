import Shared.PNP.Record285.ProjectionCertificate

/-! The 21-register pre-projection graph has the literal machine's event
behavior. The producer-packet extraction and earlier source passes remain
separate obligations. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.RegisterProjection
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore

theorem related_run (n : Nat) : Rel lift expandedRows
    ((system originalRows).run n) ((system expandedRows).run n) := by
  induction n with
  | zero => exact initial_related lift originalRows expandedRows projection_checked
  | succ n ih =>
    have hs := (step_related lift lift_injective originalRows expandedRows projection_checked
      ((system originalRows).run n) ((system expandedRows).run n) ih).2
    simpa only [EventSystem.run_succ,system] using hs

/-- Every retained slot agrees at every step, including the unbounded tail. -/
theorem retained_registers (n j : Nat) :
    ((system originalRows).run n).bank (lift j) = ((system expandedRows).run n).bank j :=
  (related_run n).2.2.1 j

/-- The three omitted source slots are never written from the all-zero entry. -/
theorem omitted_registers_zero (n k : Nat) (hk : k = 8 ∨ k = 9 ∨ k = 10) :
    ((system originalRows).run n).bank k = 0 :=
  (related_run n).2.2.2 k (omitted_not_in_image k hk)

noncomputable def acceptedProjection : EventRefinement (system originalRows) (system expandedRows) :=
  (simulation lift lift_injective originalRows expandedRows projection_checked).toEventRefinement

theorem eventuallySilent_iff_blank_start :
    (system originalRows).EventuallySilent ↔ Record285.machine.system.EventuallySilent :=
  acceptedProjection.eventuallySilent_iff.trans expanded_eventuallySilent_iff_blank_start

theorem infinitelyMany_iff_blank_start :
    (system originalRows).InfinitelyManyBeeps ↔ Record285.machine.system.InfinitelyManyBeeps :=
  acceptedProjection.infinitelyManyBeeps_iff.trans expanded_infinitelyMany_iff_blank_start

end Shared.PNP.Record285.RegisterProjection
