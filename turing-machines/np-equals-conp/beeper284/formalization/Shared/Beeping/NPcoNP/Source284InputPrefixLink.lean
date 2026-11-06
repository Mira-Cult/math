import Shared.Beeping.NPcoNP.Source284InputPrefixScanner
import Shared.Beeping.NPcoNP.Source284WindowLink

/-! A fixed two-state input scanner linked to an arbitrary finite continuation.
It starts with the original input and certificate on the source tape, reads
exactly the framed input prefix, and transfers control after its delimiter.
It does not yet copy or canonically pack that prefix for the window verifier. -/
namespace Shared.Beeping.NPcoNP.Source284InputPrefixLink

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284ListTables (Rows)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284WitnessScanArithmetic (pushPairs)
open Shared.Beeping.NPcoNP.Source284WindowLink

/-- Two finite rows scan marker and payload; destination two is the
continuation's relocated first state. -/
def rows : Rows :=
  [(⟨false,false,some 2⟩,⟨true,false,some 1⟩),
   (⟨false,false,some 0⟩,⟨true,false,some 0⟩)]

theorem loader_closed : LoaderClosed rows := by
  intro q hq b q' hn
  have hq' : q = 0 ∨ q = 1 := by simp [rows] at hq; omega
  rcases hq' with rfl | rfl <;> cases b <;>
    simp [rows,Source284ListTables.table] at hn <;> simp [rows] <;> omega

theorem marker_row (verifier : Nat → Bool → Row) (b : Bool) :
    table rows verifier 0 b = ⟨b,false,some (if b then 1 else 2)⟩ := by
  cases b <;> rfl

theorem payload_row (verifier : Nat → Bool → Row) (b : Bool) :
    table rows verifier 1 b = ⟨b,false,some 0⟩ := by
  cases b <;> rfl

theorem marker_step (verifier : Nat → Bool → Row) (left right : Nat) :
    step (table rows verifier) ⟨left,right,some 0⟩ =
      ⟨2*left+right%2,right/2,some (if right.testBit 0 then 1 else 2)⟩ := by
  simp [step,marker_row,Nat.testBit_zero,
    Source284WitnessScanner.bit_decide_mod]

theorem payload_step (verifier : Nat → Bool → Row) (left right : Nat) :
    step (table rows verifier) ⟨left,right,some 1⟩ =
      ⟨2*left+right%2,right/2,some 0⟩ := by
  simp [step,payload_row,Nat.testBit_zero,
    Source284WitnessScanner.bit_decide_mod]

theorem run_add (verifier : Nat → Bool → Row) (c : Config) (a b : Nat) :
    run (table rows verifier) c (a+b) = run (table rows verifier) (run (table rows verifier) c a) b := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
    change step (table rows verifier) (run (table rows verifier) c (a+b)) =
      step (table rows verifier) (run (table rows verifier) (run (table rows verifier) c a) b)
    rw [ih]

theorem marker_payload (verifier : Nat → Bool → Row) (left suffix : Nat) (b : Bool) (rest : List Bool) :
    run (table rows verifier) ⟨left,encodeFrame (b::rest) suffix,some 0⟩ 2 =
      ⟨4*left+2+(if b then 1 else 0),encodeFrame rest suffix,some 0⟩ := by
  cases b <;> simp [run,marker_step,payload_step,encodeFrame,
    Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> congr 1 <;> omega

/-- The scanner takes exactly two steps per payload and one for the
zero delimiter. The entire certificate and unread input suffix are retained. -/
theorem scan_frame (verifier : Nat → Bool → Row) (w : List Bool) (certificate suffix : Nat) :
    run (table rows verifier) ⟨certificate,encodeFrame w suffix,some 0⟩ (2*w.length+1) =
      ⟨2*pushPairs certificate w,suffix,some 2⟩ := by
  induction w generalizing certificate with
  | nil => simp [run,marker_step,encodeFrame,pushPairs,Nat.testBit_zero]
  | cons b bs ih =>
    have ht : 2*(b::bs).length+1 = 2+(2*bs.length+1) := by simp; omega
    rw [ht,run_add,marker_payload]
    simpa [pushPairs] using ih (4*certificate+2+(if b then 1 else 0))

/-- The actual numeric source table starts at the raw two tape halves and
reaches the linked continuation after the stated positive finite time. -/
theorem source_scan_frame (states : Nat) (verifier : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states verifier) :
    Source284Relative.run (description rows states verifier)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (2*w.length+1) =
        ⟨2*pushPairs certificate w,suffix,active 2⟩ := by
  have hvalid : Valid (rows.length+states) ⟨certificate,encodeFrame w suffix,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    subst q
    simp [rows]
  have h := run_toSource (rows.length+states) (table rows verifier) 1
    ⟨certificate,encodeFrame w suffix,some 0⟩ (closed rows states verifier hn loader_closed hv)
    hvalid (2*w.length+1)
  change Source284Relative.run (description rows states verifier)
    (Source284Relative.initial (encodeFrame w suffix) certificate) _ = _ at h
  rw [h,scan_frame]
  rfl

/-- Every numeric input, including one whose delimiter is a virtual zero,
has a finite scan whose cost is exactly linear in the parsed prefix length.
The decomposition is a proof device, not additional runtime input. -/
theorem source_total_progress (states : Nat) (verifier : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states verifier) :
    ∃ (w : List Bool) (suffix : Nat),
      encodeFrame w suffix = input ∧
      w.length = Source284Parser.length input ∧
      0 < 2*w.length+1 ∧
      Source284Relative.run (description rows states verifier)
        (Source284Relative.initial input certificate) (2*w.length+1) =
          ⟨2*pushPairs certificate w,suffix,active 2⟩ := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,by omega,?_⟩
  rw [← hw]
  exact source_scan_frame states verifier w certificate suffix hn hv

/-- The two halves at the handoff still determine the complete original
input and certificate. This is a finite arithmetic inverse given the scan
length; it does not claim that a source table has executed the inverse. -/
theorem handoff_information (w : List Bool) (certificate suffix : Nat) :
    Source284LoaderAlgebra.transfer (2*w.length+1) suffix (2*pushPairs certificate w) =
      (encodeFrame w suffix,certificate) :=
  Source284WitnessScanArithmetic.transfer_frame_restore certificate suffix w

/-- The linked continuation is run after the scan, with no implicit tape
initialization and with the scan duration included in the source clock. -/
theorem source_after_scan (states : Nat) (verifier : Nat → Bool → Row)
    (w : List Bool) (certificate suffix clock : Nat) (hn : 0 < states) (hv : Closed states verifier) :
    Source284Relative.accepts (description rows states verifier) (encodeFrame w suffix) certificate
      (2*w.length+1+clock) =
      ((Source284Relative.run (encode states verifier 1)
        ⟨2*pushPairs certificate w,suffix,active 0⟩ clock).state == 0) := by
  apply source_after_handoff rows states verifier _ _ _ _ _ _ hn loader_closed hv
  simpa [rows] using source_scan_frame states verifier w certificate suffix hn hv

/-- On every numeric source input, the finite scan reaches the actual
continuation in a number of steps determined by the parsed prefix alone. -/
theorem source_after_total_scan (states : Nat) (verifier : Nat → Bool → Row)
    (input certificate clock : Nat) (hn : 0 < states) (hv : Closed states verifier) :
    ∃ (w : List Bool) (suffix : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.accepts (description rows states verifier) input certificate
        (2*Source284Parser.length input+1+clock) =
      ((Source284Relative.run (encode states verifier 1)
        ⟨2*pushPairs certificate w,suffix,active 0⟩ clock).state == 0) := by
  obtain ⟨w,suffix,hw,hlen,_,_⟩ := source_total_progress states verifier input certificate hn hv
  refine ⟨w,suffix,hw,hlen,?_⟩
  rw [← hlen,← hw]
  exact source_after_scan states verifier w certificate suffix clock hn hv

namespace Fixtures

open Source284WindowLink.Fixtures (accept reject)

example : Source284Relative.run (description rows 1 accept)
    (Source284Relative.initial (encodeFrame [true,false] 9) 6) 5 =
      ⟨2*pushPairs 6 [true,false],9,active 2⟩ := by decide +kernel
example : Source284Relative.accepts (description rows 1 accept) 0 7 2 = true := by decide +kernel
example : Source284Relative.accepts (description rows 1 reject) 0 7 2 = false := by decide +kernel

end Fixtures

end Shared.Beeping.NPcoNP.Source284InputPrefixLink
