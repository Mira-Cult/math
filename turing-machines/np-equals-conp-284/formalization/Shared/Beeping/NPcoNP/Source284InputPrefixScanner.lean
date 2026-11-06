import Shared.Beeping.NPcoNP.Source284WitnessScannerProgress

/-! A finite relative table scans the input's marker/payload prefix, without
changing any tape bit. It stops at a continuing boundary immediately after
the first zero marker. This is a paid component for a guarded interpreter,
not an in-place suffix eraser or a complete candidate wrapper. -/

namespace Shared.Beeping.NPcoNP.Source284InputPrefixScanner

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284WitnessScanner (bit_decide_mod)
open Shared.Beeping.NPcoNP.Source284WitnessScanArithmetic
open Shared.Beeping.NPcoNP.Source284Parser
open Shared.Beeping.NPcoNP.Source284Relative

/-- Logical states: marker, payload, and continuing delimiter boundary. -/
def table : Nat → Bool → Row
  | 0, b => ⟨b, false, some (if b then 1 else 2)⟩
  | 1, b => ⟨b, false, some 0⟩
  | _, b => ⟨b, false, some 2⟩

theorem table_closed : Closed 3 table := by
  intro q hq b q' hnext
  interval_cases q <;> cases b <;> simp_all [table] <;> omega

theorem marker_step (left right : Nat) :
    Source284TableRun.step table ⟨left, right, some 0⟩ =
      ⟨2*left + right % 2, right/2,
        some (if right.testBit 0 then 1 else 2)⟩ := by
  simp [Source284TableRun.step, table, Nat.testBit_zero, bit_decide_mod]

theorem payload_step (left right : Nat) :
    Source284TableRun.step table ⟨left, right, some 1⟩ =
      ⟨2*left + right % 2, right/2, some 0⟩ := by
  simp [Source284TableRun.step, table, Nat.testBit_zero, bit_decide_mod]

theorem run_add (c : Source284TableRun.Config) (a b : Nat) :
    Source284TableRun.run table c (a+b) =
      Source284TableRun.run table (Source284TableRun.run table c a) b := by
  induction b with
  | zero => simp [Source284TableRun.run]
  | succ b ih =>
    change Source284TableRun.step table (Source284TableRun.run table c (a+b)) =
      Source284TableRun.step table (Source284TableRun.run table (Source284TableRun.run table c a) b)
    rw [ih]

theorem marker_payload (left suffix : Nat) (b : Bool) (rest : List Bool) :
    Source284TableRun.run table ⟨left, encodeFrame (b::rest) suffix, some 0⟩ 2 =
      ⟨4*left + 2 + (if b then 1 else 0), encodeFrame rest suffix, some 0⟩ := by
  cases b <;>
    simp [Source284TableRun.run, marker_step, payload_step, encodeFrame,
      Nat.testBit_zero, Nat.add_mod, Nat.mul_mod] <;> congr 1 <;> omega

/-- The original certificate remains embedded in the first half. The
unread suffix is retained, not discarded. -/
theorem scan_frame (w : List Bool) (certificate suffix : Nat) :
    Source284TableRun.run table ⟨certificate, encodeFrame w suffix, some 0⟩
      (2*w.length+1) = ⟨2*pushPairs certificate w, suffix, some 2⟩ := by
  induction w generalizing certificate with
  | nil =>
    simp [Source284TableRun.run, marker_step, encodeFrame, pushPairs, Nat.testBit_zero]
  | cons b bs ih =>
    have htime : 2*(b::bs).length+1 = 2 + (2*bs.length+1) := by simp; omega
    rw [htime, run_add, marker_payload]
    simpa [pushPairs] using ih (4*certificate+2+(if b then 1 else 0))

theorem source_scan_frame (w : List Bool) (certificate suffix tail : Nat) :
    Source284Relative.run (encode 3 table tail)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (2*w.length+1) =
        ⟨2*pushPairs certificate w, suffix, active 2⟩ := by
  have hv : Valid 3 ⟨certificate, encodeFrame w suffix, some 0⟩ := by
    intro q h
    simp only [Option.some.injEq] at h
    omega
  have hr := run_toSource 3 table tail
    ⟨certificate, encodeFrame w suffix, some 0⟩ table_closed hv (2*w.length+1)
  change Source284Relative.run (encode 3 table tail)
    (Source284Relative.initial (encodeFrame w suffix) certificate) _ = _ at hr
  rw [hr, scan_frame]
  rfl

/-- Every numeric input reaches the boundary, including inputs with a
virtual zero delimiter; the source parser determines the exact time. -/
theorem source_total_progress (input certificate tail : Nat) :
    ∃ (w : List Bool) (suffix : Nat),
      encodeFrame w suffix = input ∧
      w.length = Source284Parser.length input ∧
      0 < 2*w.length+1 ∧
      2*w.length+1 ≤ 2*Nat.size input+1 ∧
      Source284Relative.run (encode 3 table tail)
        (Source284Relative.initial input certificate) (2*w.length+1) =
          ⟨2*pushPairs certificate w, suffix, active 2⟩ := by
  obtain ⟨w, suffix, hw⟩ := encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length, parse_encodeFrame]
  have hsize : w.length ≤ Nat.size input := by
    rw [← hlen]
    exact Shared.Beeping.NPcoNP.Source284WitnessInputBound.parsed_length_le_size input
  refine ⟨w, suffix, hw, hlen.symm, by omega, by omega, ?_⟩
  rw [← hw]
  exact source_scan_frame w certificate suffix tail

end Shared.Beeping.NPcoNP.Source284InputPrefixScanner
