import Shared.Beeping.NPcoNP.Source284InputSentinel

/-! A four-mode input-prefix scanner. Its control carries the two certificate
bits saved by `Source284InputSentinel`; the scanned tape retains a genuine
`00` boundary beneath the framed input. The table reaches an arbitrary
finite continuation. It does not yet implement a self-delimiting return or the
canonical packed-window loader. -/
namespace Shared.Beeping.NPcoNP.Source284ModePrefixScan

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284WitnessScanArithmetic (pushPairs)

/-- Four marker modes, four payload modes, then the continuation. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q < 4 then ⟨b,false,some (if b then q+4 else q+8)⟩
  else if q < 8 then ⟨b,false,some (q-4)⟩
  else shiftRow 8 (continuation (q-8) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 4 ≤ states) (hv : Closed states continuation) : Closed (8+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases h0 : q < 4
  · cases b <;> simp [table,h0] at hnext <;> omega
  · by_cases h1 : q < 8
    · simp [table,h0,h1] at hnext
      omega
    · have hnext' : (shiftRow 8 (continuation (q-8) b)).next = some q' := by
        simpa [table,h0,h1] using hnext
      have hq0 : q-8 < states := by omega
      cases ht : (continuation (q-8) b).next with
      | none => simp [shiftRow,ht] at hnext'
      | some target =>
        have hh := hv (q-8) hq0 b target ht
        simp [shiftRow,ht] at hnext'
        subst q'
        omega

theorem marker_row (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4) (b : Bool) :
    table continuation mode b = ⟨b,false,some (if b then mode+4 else mode+8)⟩ := by
  simp [table,hm]

theorem payload_row (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4) (b : Bool) :
    table continuation (mode+4) b = ⟨b,false,some mode⟩ := by
  have h0 : ¬ mode+4 < 4 := by omega
  have h1 : mode+4 < 8 := by omega
  simp [table,h0,h1]

theorem marker_step (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left right : Nat) :
    step (table continuation) ⟨left,right,some mode⟩ =
      ⟨2*left+right%2,right/2,some (if right.testBit 0 then mode+4 else mode+8)⟩ := by
  simp [step,marker_row _ _ hm,Nat.testBit_zero,Source284WitnessScanner.bit_decide_mod]

theorem payload_step (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left right : Nat) :
    step (table continuation) ⟨left,right,some (mode+4)⟩ =
      ⟨2*left+right%2,right/2,some mode⟩ := by
  simp [step,payload_row _ _ hm,Nat.testBit_zero,Source284WitnessScanner.bit_decide_mod]

theorem run_add (t : Nat → Bool → Row) (c : Config) (a b : Nat) :
    run t c (a+b) = run t (run t c a) b := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
    change step t (run t c (a+b)) = step t (run t (run t c a) b)
    rw [ih]

theorem marker_payload (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left suffix : Nat) (b : Bool) (rest : List Bool) :
    run (table continuation) ⟨left,encodeFrame (b::rest) suffix,some mode⟩ 2 =
      ⟨4*left+2+(if b then 1 else 0),encodeFrame rest suffix,some mode⟩ := by
  cases b <;> simp [run,marker_step _ _ hm,payload_step _ _ hm,encodeFrame,
    Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> congr 1 <;> omega

/-- Scan the complete frame and retain the mode in the continuation state. -/
theorem scan_frame (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (w : List Bool) (left suffix : Nat) :
    run (table continuation) ⟨left,encodeFrame w suffix,some mode⟩ (2*w.length+1) =
      ⟨2*pushPairs left w,suffix,some (8+mode)⟩ := by
  induction w generalizing left with
  | nil => simp [run,marker_step _ _ hm,encodeFrame,pushPairs,Nat.testBit_zero,Nat.add_comm]
  | cons b bs ih =>
    have ht : 2*(b::bs).length+1 = 2+(2*bs.length+1) := by simp; omega
    rw [ht,run_add,marker_payload _ _ hm]
    simpa [pushPairs] using ih (4*left+2+(if b then 1 else 0))

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (8+q) b = shiftRow 8 (continuation q b) := by
  have h4 : ¬ 8+q < 4 := by omega
  have h8 : ¬ 8+q < 8 := by omega
  simp [table,h4,h8]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 8 c) = shiftConfig 8 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (table continuation) (shiftConfig 8 c) clock = shiftConfig 8 (run continuation c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp only [run,ih,relocated_step]

/-- The real source table first saves the two low certificate bits and then
scans the input. Every transition is paid; no preloaded boundary is assumed. -/
theorem source_prepare_scan (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 4 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (Source284InputSentinel.description (8+states) (table continuation))
      (Source284Relative.initial (encodeFrame w suffix) certificate) (4+(2*w.length+1)) =
      ⟨2*pushPairs (4*(certificate/4)) w,suffix,active (16+certificate%4)⟩ := by
  have hc : Closed (8+states) (table continuation) := closed states continuation hn hv
  have hcs : Closed (8+(8+states)) (Source284InputSentinel.table (table continuation)) :=
    Source284InputSentinel.closed (8+states) (table continuation) (by omega) hc
  have hvalid : Valid (8+(8+states)) ⟨certificate,encodeFrame w suffix,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    subst q
    omega
  have hr := run_toSource (8+(8+states)) (Source284InputSentinel.table (table continuation)) 1
    ⟨certificate,encodeFrame w suffix,some 0⟩ hcs hvalid (4+(2*w.length+1))
  change Source284Relative.run (Source284InputSentinel.description (8+states) (table continuation))
    (Source284Relative.initial (encodeFrame w suffix) certificate) _ = _ at hr
  rw [hr,run_add,Source284InputSentinel.prepare]
  have hm : certificate%4 < 4 := Nat.mod_lt certificate (by decide)
  change toSource (run (Source284InputSentinel.table (table continuation))
    (shiftConfig 8 ⟨4*(certificate/4),encodeFrame w suffix,some (certificate%4)⟩) _) = _
  rw [Source284InputSentinel.relocated_run,scan_frame _ _ hm]
  simp [toSource,shiftConfig,nextState,active]
  omega

/-- Every raw numeric input reaches the continuation in finite time bounded
by its parsed prefix length, including virtual-zero termination. -/
theorem source_total_progress (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 4 ≤ states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (Source284InputSentinel.description (8+states) (table continuation))
        (Source284Relative.initial input certificate) (4+(2*w.length+1)) =
      ⟨2*pushPairs (4*(certificate/4)) w,suffix,active (16+certificate%4)⟩ := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_⟩
  rw [← hw]
  exact source_prepare_scan states continuation w certificate suffix hn hv

/-- The resulting data and four-way mode determine both original halves,
and the low two bits of the retained certificate half are zero. The transfer
is a mathematical inverse given the scan length, not an implemented return. -/
theorem handoff_information (w : List Bool) (certificate suffix : Nat) :
    Source284LoaderAlgebra.transfer (2*w.length+1) suffix
        (2*pushPairs (4*(certificate/4)) w) =
          (encodeFrame w suffix,4*(certificate/4)) ∧
      4*(certificate/4)+certificate%4 = certificate ∧
      4*(certificate/4)%4 = 0 := by
  exact ⟨Source284WitnessScanArithmetic.transfer_frame_restore (4*(certificate/4)) suffix w,
    Source284InputSentinel.certificate_recovered certificate,
    Source284InputSentinel.cleared_low_bits certificate⟩

/-- After preparing and scanning, the supplied continuation receives its
entry mode and exact tape halves. The entire prefix cost is included. -/
theorem source_after_prepare_scan (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix clock : Nat) (hn : 4 ≤ states)
    (hv : Closed states continuation) :
    Source284Relative.accepts (Source284InputSentinel.description (8+states) (table continuation))
      (encodeFrame w suffix) certificate (4+(2*w.length+1)+clock) =
    ((Source284Relative.run (encode states continuation 1)
      ⟨2*pushPairs (4*(certificate/4)) w,suffix,active (certificate%4)⟩ clock).state == 0) := by
  have hm : certificate%4 < states := by
    have h := Nat.mod_lt certificate (by decide : 0 < 4)
    omega
  let c : Config := ⟨2*pushPairs (4*(certificate/4)) w,suffix,some (certificate%4)⟩
  have h0 : Valid states c := by
    intro q hq
    simp [c] at hq
    subst q
    exact hm
  have h1 : Valid (8+(8+states)) (shiftConfig 8 (shiftConfig 8 c)) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hc := closed states continuation hn hv
  have hr1 := run_toSource (8+(8+states)) (Source284InputSentinel.table (table continuation)) 1
    (shiftConfig 8 (shiftConfig 8 c))
    (Source284InputSentinel.closed (8+states) (table continuation) (by omega) hc) h1 clock
  have hr0 := run_toSource states continuation 1 c hv h0 clock
  have hs : 8+(8+certificate%4) = 16+certificate%4 := by omega
  change Source284Relative.run (Source284InputSentinel.description (8+states) (table continuation))
    ⟨2*pushPairs (4*(certificate/4)) w,suffix,active (8+(8+certificate%4))⟩ clock = _ at hr1
  rw [hs] at hr1
  change Source284Relative.run (encode states continuation 1)
    ⟨2*pushPairs (4*(certificate/4)) w,suffix,active (certificate%4)⟩ clock = _ at hr0
  unfold Source284Relative.accepts
  rw [Source284Relative.run_add_clock,source_prepare_scan states continuation w certificate suffix hn hv,
    hr1,hr0,Source284InputSentinel.relocated_run,relocated_run]
  cases h : (run continuation c clock).state <;>
    simp [toSource,shiftConfig,nextState,h,active]

end Shared.Beeping.NPcoNP.Source284ModePrefixScan
