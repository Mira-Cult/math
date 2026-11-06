import Shared.Beeping.NPcoNP.Source284RawScannerCutoff
import Shared.Beeping.NPcoNP.Source284ClockStability

/-! Marker-state entry point for the finite scanner's raw-certificate cutoff
observation. This permits a separately paid initializer to enter the scanner
without paying its initial turn twice. The result does not count the scanner
steps internally, enforce rejection, erase high bits, or construct a verifier. -/

namespace Shared.Beeping.NPcoNP.Source284RawMarkerCutoff

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284WitnessScanner
open Shared.Beeping.NPcoNP.Source284RawScannerCutoff

/-- Starting already on the marker, the finite encoded scanner observes
window rejection after exactly `2*limit+1` further transitions, including
arbitrary high bits of the certificate and arbitrary table-encoding tail. -/
theorem marker_source_reject (limit certificate left tail : Nat) :
    (Source284Relative.run (encode 4 table tail) ⟨left, certificate, 3⟩
      (2*limit+1)).state = 5 ↔
      Shared.Beeping.NPcoNP.Source284WitnessWindow.decode limit certificate = none := by
  have hstart : Source284Relative.run (encode 4 table tail)
      (Source284Relative.initial left certificate) 1 = ⟨left, certificate, 3⟩ := by
    rw [source_run]
    change Source284TableRun.toSource
      (Source284TableRun.step table ⟨certificate, left, some 0⟩) = _
    rw [initial_turn]
    rfl
  have h := raw_source_reject limit certificate left tail
  have ht : 2*limit+2 = 1+(2*limit+1) := by omega
  rw [ht, Source284Relative.run_add_clock, hstart] at h
  exact h


/-- Every scanner control reachable from the marker remains among its four
logical states, represented by source control numbers below eight. -/
theorem marker_source_state_lt_eight (certificate left tail steps : Nat) :
    (Source284Relative.run (encode 4 table tail) ⟨left, certificate, 3⟩ steps).state < 8 := by
  let c : Source284TableRun.Config := ⟨left, certificate, some 1⟩
  have hv : Source284TableRun.Valid 4 c := by
    intro q hq
    simp only [c, Option.some.injEq] at hq
    omega
  have hf := Source284TableRun.valid_run 4 table c table_closed hv steps
  have hr := Source284TableRun.run_toSource 4 table tail c table_closed hv steps
  change Source284Relative.run (encode 4 table tail) ⟨left, certificate, 3⟩ steps = _ at hr
  rw [hr]
  change nextState (Source284TableRun.run table c steps).state < 8
  cases hs : (Source284TableRun.run table c steps).state with
  | none => simp [nextState]
  | some q =>
    have hq := hf q hs
    simp only [nextState, active]
    omega

end Shared.Beeping.NPcoNP.Source284RawMarkerCutoff
