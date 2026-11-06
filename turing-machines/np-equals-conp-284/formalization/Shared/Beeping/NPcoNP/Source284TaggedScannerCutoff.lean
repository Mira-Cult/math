import Shared.Beeping.NPcoNP.Source284TaggedScannerRun
import Shared.Beeping.NPcoNP.Source284RawMarkerCutoff
import Shared.Beeping.NPcoNP.Source284TaggedWitnessCodec

/-! Finite fixed-time observation of tagged window-decoder rejection by the
combined source tag gate and marker scanner. The raw certificate is not
physically truncated; only its observable low window is relevant. No machine
counter waits for this time, and no rejection route, witness verifier, clock
or physical beeper refinement is supplied by this theorem. -/

namespace Shared.Beeping.NPcoNP.Source284TaggedScannerCutoff

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TaggedScanner
open Shared.Beeping.NPcoNP.Source284RawMarkerCutoff
open Shared.Beeping.NPcoNP.Source284RawScannerCutoff

/-- Invalid tag or overlong bounded-window witness is observable in one of
two continuing states, at a fixed time that includes the paid tag check.
This begins at the source evaluator’s supplied input/certificate configuration;
it does not establish blank-tape physical initialization. -/
theorem source_reject_iff (m c i tail : Nat) :
    let state := (Source284Relative.run (description tail)
      (Source284Relative.initial i c) (2*m+4)).state
    (state = 5 ∨ state = 13) ↔
      Shared.Beeping.NPcoNP.Source284TaggedWitnessCodec.decode m c = none := by
  dsimp only
  have ht : 2*m+4 = 3+(2*m+1) := by omega
  rw [ht]
  by_cases h : c%4 = 0
  · rw [source_valid_state c i (2*m+1) tail 0 h]
    have hs := raw_source_reject m (c/4) (4*i) 0
    have hb := marker_source_state_lt_eight (c/4) (4*i) 0 (2*m+1)
    have hstart : Source284Relative.run
        (encode 4 Shared.Beeping.NPcoNP.Source284WitnessScanner.table 0)
        (Source284Relative.initial (4*i) (c/4)) 1 = ⟨4*i,c/4,3⟩ := by
      rw [Shared.Beeping.NPcoNP.Source284WitnessScanner.source_run]
      change Shared.Beeping.NPcoNP.Source284TableRun.toSource
        (Shared.Beeping.NPcoNP.Source284TableRun.step
          Shared.Beeping.NPcoNP.Source284WitnessScanner.table ⟨c/4,4*i,some 0⟩) = _
      rw [Shared.Beeping.NPcoNP.Source284WitnessScanner.initial_turn]
      rfl
    have htime : 2*m+2 = 1+(2*m+1) := by omega
    rw [htime, Source284Relative.run_add_clock, hstart] at hs
    simp only [Shared.Beeping.NPcoNP.Source284TaggedWitnessCodec.decode, h, ↓reduceIte]
    rw [Source284Relative.run_add_clock, hstart]
    have hb' : (Source284Relative.run
        (encode 4 Shared.Beeping.NPcoNP.Source284WitnessScanner.table 0)
        ⟨4*i,c/4,3⟩ (2*m+1)).state ≠ 13 := by omega
    simp only [hb', or_false]
    exact hs
  · rw [source_invalid_state c i (2*m+1) tail h]
    simp [active, Shared.Beeping.NPcoNP.Source284TaggedWitnessCodec.decode, h]

end Shared.Beeping.NPcoNP.Source284TaggedScannerCutoff
