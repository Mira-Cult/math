import Shared.Beeping.NPcoNP.Source284ModePrefixScan
import Shared.Beeping.NPcoNP.Source284TaggedWitnessRoundtrip

/-! A finite return scanner for the `00` boundary built by the mode-preserving
input scan. It detects the boundary without a preloaded length, restores the
saved certificate bits, and hands control to a supplied finite continuation.
This is not yet the packed-window loader or a physical-machine refinement. -/
namespace Shared.Beeping.NPcoNP.Source284ModePrefixReturn

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284WitnessScanArithmetic (pushPairs)
open Shared.Beeping.NPcoNP.Source284TaggedWitnessRoundtrip (pushPairs_snoc rawPairs rawPairs_append rawPairs_frame)

/-- Four entry modes; the prefix traverses the input in reverse until the
reserved `00`, restores the two saved certificate bits, and enters state 32. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q < 4 then ⟨b,true,some (q+4)⟩
  else if q < 8 then ⟨b,false,some (q+4)⟩
  else if q < 12 then ⟨b,false,some (12+2*(q-8)+bit b)⟩
  else if q < 20 then ⟨b,false,some (if b then 8+(q-12)/2 else 20+(q-12)/2)⟩
  else if q < 24 then ⟨b,true,some (q+4)⟩
  else if q < 28 then ⟨decide ((q-24)/2 = 1),false,some (q+4)⟩
  else if q < 32 then ⟨decide ((q-28)%2 = 1),false,some 32⟩
  else shiftRow 32 (continuation (q-32) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (32+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases h0 : q < 4
  · simp [table,h0] at hnext; omega
  · by_cases h1 : q < 8
    · simp [table,h0,h1] at hnext; omega
    · by_cases h2 : q < 12
      · cases b <;> simp [table,h0,h1,h2,bit] at hnext <;> omega
      · by_cases h3 : q < 20
        · cases b <;> simp [table,h0,h1,h2,h3] at hnext <;> omega
        · by_cases h4 : q < 24
          · simp [table,h0,h1,h2,h3,h4] at hnext; omega
          · by_cases h5 : q < 28
            · simp [table,h0,h1,h2,h3,h4,h5] at hnext; omega
            · by_cases h6 : q < 32
              · simp [table,h0,h1,h2,h3,h4,h5,h6] at hnext; omega
              · have ht : (shiftRow 32 (continuation (q-32) b)).next = some q' := by
                  simpa [table,h0,h1,h2,h3,h4,h5,h6] using hnext
                have hq0 : q-32 < states := by omega
                cases hh : (continuation (q-32) b).next with
                | none => simp [shiftRow,hh] at ht
                | some r =>
                  have h := hv (q-32) hq0 b r hh
                  simp [shiftRow,hh] at ht
                  subst q'
                  omega

theorem run_add (continuation : Nat → Bool → Row) (c : Config) (a b : Nat) :
    run (table continuation) c (a+b) = run (table continuation) (run (table continuation) c a) b := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
    change step (table continuation) (run (table continuation) c (a+b)) =
      step (table continuation) (run (table continuation) (run (table continuation) c a) b)
    rw [ih]

/-- Turn and pass the frame delimiter, preserving the saved-bit mode. -/
theorem start (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left suffix : Nat) :
    run (table continuation) ⟨2*left,suffix,some mode⟩ 2 =
      ⟨2*suffix,left,some (8+mode)⟩ := by
  interval_cases mode <;>
    simp [run,step,table,bit,Nat.testBit_zero,Source284WitnessScanner.bit_decide_mod] <;>
    congr 1 <;> split_ifs <;> omega

/-- Read one reversed payload and its required one marker. -/
theorem reverse_pair (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left right : Nat) (b : Bool) :
    run (table continuation) ⟨left,4*right+2+(if b then 1 else 0),some (8+mode)⟩ 2 =
      ⟨4*left+2*(if b then 1 else 0)+1,right,some (8+mode)⟩ := by
  interval_cases mode <;> cases b <;>
    simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;>
    congr 1 <;> split_ifs <;> omega

theorem reverse_pairs (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (w : List Bool) (left right : Nat) :
    run (table continuation) ⟨left,pushPairs right w,some (8+mode)⟩ (2*w.length) =
      ⟨rawPairs w left,right,some (8+mode)⟩ := by
  induction w using List.reverseRecOn generalizing left with
  | nil => simp [run,pushPairs,rawPairs]
  | append_singleton w b ih =>
    rw [pushPairs_snoc]
    have ht : 2*(w ++ [b]).length = 2+2*w.length := by simp; omega
    rw [ht,run_add,reverse_pair _ _ hm,ih,rawPairs_append]
    rfl

/-- The next two zeros terminate the reverse scan. -/
theorem boundary (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left higher : Nat) :
    run (table continuation) ⟨left,4*higher,some (8+mode)⟩ 2 =
      ⟨4*left,higher,some (20+mode)⟩ := by
  interval_cases mode <;> simp [run,step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;>
    congr 1 <;> split_ifs <;> omega

/-- Reinsert the saved second and first bits and return the head to the
original input boundary. -/
theorem restore (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (input higher : Nat) :
    run (table continuation) ⟨4*input,higher,some (20+mode)⟩ 3 =
      ⟨4*higher+mode,input,some 32⟩ := by
  interval_cases mode <;>
    simp [run,step,table,bit,Nat.testBit_zero,Nat.mul_mod,
      Source284WitnessScanner.bit_decide_mod] <;> congr 1 <;> split_ifs <;> omega

/-- The return is self-delimiting: the program tests tape markers, while the
proof's `w` is used only to state its exact finite execution time. -/
theorem return_frame (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (w : List Bool) (higher suffix : Nat) :
    run (table continuation) ⟨2*pushPairs (4*higher) w,suffix,some mode⟩ (2*w.length+7) =
      ⟨4*higher+mode,encodeFrame w suffix,some 32⟩ := by
  have ht : 2*w.length+7 = 2+(2*w.length)+2+3 := by omega
  rw [ht,run_add,run_add,run_add,start _ _ hm,reverse_pairs _ _ hm,rawPairs_frame,
    boundary _ _ hm,restore _ _ hm]

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (32+q) b = shiftRow 32 (continuation q b) := by
  have h4 : ¬ 32+q < 4 := by omega
  have h8 : ¬ 32+q < 8 := by omega
  have h12 : ¬ 32+q < 12 := by omega
  have h20 : ¬ 32+q < 20 := by omega
  have h24 : ¬ 32+q < 24 := by omega
  have h28 : ¬ 32+q < 28 := by omega
  have h32 : ¬ 32+q < 32 := by omega
  simp [table,h4,h8,h12,h20,h24,h28,h32]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 32 c) = shiftConfig 32 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (table continuation) (shiftConfig 32 c) clock = shiftConfig 32 (run continuation c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp only [run,ih,relocated_step]

/-- The source-level return restores both halves and reaches the relocated
continuation. The saved-bit mode is encoded in the machine state. -/
theorem source_return_frame (states : Nat) (continuation : Nat → Bool → Row)
    (mode : Nat) (hm : mode < 4) (w : List Bool) (higher suffix : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run
      (Source284InputSentinel.description (8+(32+states))
        (Source284ModePrefixScan.table (table continuation)))
      ⟨2*pushPairs (4*higher) w,suffix,active (16+mode)⟩ (2*w.length+7) =
      ⟨4*higher+mode,encodeFrame w suffix,active 48⟩ := by
  let c : Config := ⟨2*pushPairs (4*higher) w,suffix,some mode⟩
  have hc := closed states continuation hn hv
  have hcm := Source284ModePrefixScan.closed (32+states) (table continuation) (by omega) hc
  have hcs := Source284InputSentinel.closed (8+(32+states))
    (Source284ModePrefixScan.table (table continuation)) (by omega) hcm
  have hvalid : Valid (8+(8+(32+states))) (shiftConfig 8 (shiftConfig 8 c)) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := run_toSource (8+(8+(32+states)))
    (Source284InputSentinel.table (Source284ModePrefixScan.table (table continuation))) 1
    (shiftConfig 8 (shiftConfig 8 c)) hcs hvalid (2*w.length+7)
  have hs : 8+(8+mode) = 16+mode := by omega
  change Source284Relative.run
      (Source284InputSentinel.description (8+(32+states))
        (Source284ModePrefixScan.table (table continuation)))
      ⟨2*pushPairs (4*higher) w,suffix,active (8+(8+mode))⟩ _ = _ at hr
  rw [hs] at hr
  rw [hr,Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,
    return_frame _ _ hm]
  rfl

/-- From the raw two halves the table scans the frame, finds its own
boundary, restores both halves, and enters the continuation in exactly
`4*n+12` steps. The input length is not preloaded. -/
theorem source_roundtrip (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run
      (Source284InputSentinel.description (8+(32+states))
        (Source284ModePrefixScan.table (table continuation)))
      (Source284Relative.initial (encodeFrame w suffix) certificate) (4*w.length+12) =
      ⟨certificate,encodeFrame w suffix,active 48⟩ := by
  have hm : certificate%4 < 4 := Nat.mod_lt certificate (by decide)
  have ht : 4*w.length+12 = (4+(2*w.length+1))+(2*w.length+7) := by omega
  have hc := closed states continuation hn hv
  rw [ht,Source284Relative.run_add_clock,
    Source284ModePrefixScan.source_prepare_scan (32+states) (table continuation) w certificate suffix
      (by omega) hc,
    source_return_frame states continuation (certificate%4) hm w (certificate/4) suffix hn hv,
    Source284InputSentinel.certificate_recovered]

/-- This execution theorem applies to every numeric input; the parser's
length fixes the proof bound, not a runtime-provided clock. -/
theorem source_total_progress (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run
      (Source284InputSentinel.description (8+(32+states))
        (Source284ModePrefixScan.table (table continuation)))
      (Source284Relative.initial input certificate) (4*Source284Parser.length input+12) =
      ⟨certificate,input,active 48⟩ := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  rw [hlen,← hw]
  exact source_roundtrip states continuation w certificate suffix hn hv

/-- After the finite, paid scan and return, the original finite continuation
runs on the untouched raw input and certificate. -/
theorem source_after_roundtrip (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate clock : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.accepts
      (Source284InputSentinel.description (8+(32+states))
        (Source284ModePrefixScan.table (table continuation)))
      input certificate (4*Source284Parser.length input+12+clock) =
      Source284Relative.accepts (encode states continuation 1) input certificate clock := by
  let c : Config := ⟨certificate,input,some 0⟩
  have h0 : Valid states c := by
    intro q hq
    simp [c] at hq
    subst q
    exact hn
  have h1 : Valid (8+(8+(32+states))) (shiftConfig 8 (shiftConfig 8 (shiftConfig 32 c))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hc := closed states continuation hn hv
  have hcm := Source284ModePrefixScan.closed (32+states) (table continuation) (by omega) hc
  have hcs := Source284InputSentinel.closed (8+(32+states))
    (Source284ModePrefixScan.table (table continuation)) (by omega) hcm
  have hr1 := run_toSource (8+(8+(32+states)))
    (Source284InputSentinel.table (Source284ModePrefixScan.table (table continuation))) 1
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 32 c))) hcs h1 clock
  have hr0 := run_toSource states continuation 1 c hv h0 clock
  change Source284Relative.run
      (Source284InputSentinel.description (8+(32+states))
        (Source284ModePrefixScan.table (table continuation)))
      ⟨certificate,input,active (8+(8+32))⟩ clock = _ at hr1
  have hs : 8+(8+32) = 48 := by omega
  rw [hs] at hr1
  change Source284Relative.run (encode states continuation 1)
      (Source284Relative.initial input certificate) clock = _ at hr0
  unfold Source284Relative.accepts
  rw [Source284Relative.run_add_clock,source_total_progress states continuation input certificate hn hv,
    hr1,hr0,Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,relocated_run]
  cases h : (run continuation c clock).state <;>
    simp [toSource,shiftConfig,nextState,h,active]

-- Empty frame with an ignored nonzero suffix, and a two-bit frame with
-- saved low bits `11` and nonzero high certificate data.
example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run
      (Source284InputSentinel.description (8+(32+states))
        (Source284ModePrefixScan.table (table continuation)))
      (Source284Relative.initial (encodeFrame [] 19) 0) 12 =
      ⟨0,encodeFrame [] 19,active 48⟩ := by
  simpa using source_roundtrip states continuation [] 0 19 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run
      (Source284InputSentinel.description (8+(32+states))
        (Source284ModePrefixScan.table (table continuation)))
      (Source284Relative.initial (encodeFrame [true,false] 19) 7) 20 =
      ⟨7,encodeFrame [true,false] 19,active 48⟩ := by
  simpa using source_roundtrip states continuation [true,false] 7 19 hn hv

end Shared.Beeping.NPcoNP.Source284ModePrefixReturn
