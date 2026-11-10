import PASoundness.M236HistoricalGuard
import PASoundness.PAtoCompactEndToEndProofTranslation

/-! Direct composition for the historical-style omega observer.

`M236HistoricalGuard.HistoricalAccept` is the Lean transcription of the
guard and first-record acceptance predicate in omega-semantics.md §§1–2 at
commit `60c6f2c22ddd50d3ba40e2ca94a4a63a87e74a0c`. Its comparison with the
manuscript is a separate review judgment. This corollary does not identify
the historical normalized-PA-proof record coding with the selected compact
source record coding.
-/
namespace PASoundness.M236HistoricalPASoundness

open FirstOrder FirstOrder.Language
open PASoundness.M236Observer
open Shared.Beeping.Machines

/-- The historical-style guarded observer accepts the literal blank-start
M236 exactly when every PA-provable sentence is true in standard `Nat`. -/
theorem selected_historical_accept_iff_pa_soundness :
    M236HistoricalGuard.HistoricalAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  M236HistoricalGuard.selected_historicalAccept_iff_traceAccept.trans
    PAtoCompactEndToEndProofTranslation.selected_accepts_iff_pa_soundness

end PASoundness.M236HistoricalPASoundness

#print axioms PASoundness.M236HistoricalPASoundness.selected_historical_accept_iff_pa_soundness
