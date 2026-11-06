import Shared.Beeping.NPcoNP.Source284CounterSeed
import Shared.Beeping.NPcoNP.Source284ScratchFlipReturn

/-! Install an empty unary counter in the ignored high suffix of an actual
self-delimited scratch stream. The finite table flips the payload markers,
seeds the counter, and returns to the original boundary. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284ScratchCounterSeed

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284PayloadLoop (scratch)
open Shared.Beeping.NPcoNP.Source284ScratchTerminator (mark)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (push flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)

def afterSeed (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some 1⟩
  else shiftRow 1 (Source284ScratchFlipReturn.table continuation (q-1) b)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some 1⟩
  else if q = 1 then ⟨b,false,some 2⟩
  else if q = 2 then ⟨!b,b,some (if b then 3 else 1)⟩
  else if q = 3 then ⟨b,true,some 4⟩
  else shiftRow 4 (Source284CounterSeed.table (afterSeed continuation) (q-4) b)

theorem afterSeed_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (7+states) (afterSeed continuation) := by
  have hc := Source284ScratchFlipReturn.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases h0 : q=0
  · subst q; simp [afterSeed] at hnext; omega
  · have he : (shiftRow 1 (Source284ScratchFlipReturn.table continuation (q-1) b)).next = some q' := by
      simpa [afterSeed,h0] using hnext
    cases hh : (Source284ScratchFlipReturn.table continuation (q-1) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hc (q-1) (by omega) b r hh
      simp [shiftRow,hh] at he
      subst q'; omega

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (16+states) (table continuation) := by
  have hc := Source284CounterSeed.closed (7+states) (afterSeed continuation) (by omega)
    (afterSeed_closed states continuation hn hv)
  intro q hq b q' hnext
  by_cases hsmall : q < 4
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have he : (shiftRow 4 (Source284CounterSeed.table (afterSeed continuation) (q-4) b)).next = some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega,
        show q ≠ 2 by omega,show q ≠ 3 by omega] using hnext
    cases hh : (Source284CounterSeed.table (afterSeed continuation) (q-4) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hc (q-4) (by omega) b r hh
      simp [shiftRow,hh] at he
      subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (4+q) b = shiftRow 4 (Source284CounterSeed.table (afterSeed continuation) q b) := by
  simp [table,show 4+q ≠ 1 by omega,show 4+q ≠ 2 by omega,show 4+q ≠ 3 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 4 c) =
      shiftConfig 4 (step (Source284CounterSeed.table (afterSeed continuation)) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 4 c) fuel =
      shiftConfig 4 (run (Source284CounterSeed.table (afterSeed continuation)) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem after_relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (afterSeed continuation) (shiftConfig 1 c) =
      shiftConfig 1 (step (Source284ScratchFlipReturn.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,afterSeed,show 1+q ≠ 0 by omega,
        ↓reduceIte,show 1+q-1=q by omega,shiftRow]
      split <;> rfl

theorem after_relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (afterSeed continuation) (shiftConfig 1 c) fuel =
      shiftConfig 1 (run (Source284ScratchFlipReturn.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,after_relocated_step]

theorem initial (continuation : Nat → Bool → Row) (left right : Nat) :
    step (table continuation) ⟨left,2*right,some 0⟩ = ⟨2*left,right,some 1⟩ := by
  simp [step,table,bit]

theorem payload_step (continuation : Nat → Bool → Row) (left tail : Nat) (b : Bool) :
    step (table continuation) ⟨left,bit b+4*tail,some 1⟩ =
      ⟨2*left+bit b,2*tail,some 2⟩ := by
  cases b <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem marker_zero (continuation : Nat → Bool → Row) (left tail : Nat) :
    step (table continuation) ⟨left,2*tail,some 2⟩ = ⟨2*left+1,tail,some 1⟩ := by
  simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega

theorem payload_pair (continuation : Nat → Bool → Row) (left tail : Nat) (b : Bool) :
    run (table continuation) ⟨left,bit b+4*tail,some 1⟩ 2 =
      ⟨4*left+2*bit b+1,tail,some 1⟩ := by
  rw [Source284HardwireTable.run_front,payload_step,Source284HardwireTable.run_front,marker_zero]
  simp only [run]
  congr 1 <;> omega

theorem terminator (continuation : Nat → Bool → Row) (left tail : Nat) :
    run (table continuation) ⟨left,4*tail+2,some 1⟩ 3 =
      ⟨2*left,2*tail,some 4⟩ := by
  have h1 : step (table continuation) ⟨left,4*tail+2,some 1⟩ = ⟨2*left,2*tail+1,some 2⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have h2 : step (table continuation) ⟨2*left,2*tail+1,some 2⟩ = ⟨2*tail,2*left,some 3⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have h3 : step (table continuation) ⟨2*tail,2*left,some 3⟩ = ⟨2*left,2*tail,some 4⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod]
  rw [Source284HardwireTable.run_front,h1,Source284HardwireTable.run_front,h2,
    Source284HardwireTable.run_front,h3]
  rfl

theorem scan (continuation : Nat → Bool → Row) (w : List Bool) (left suffix : Nat) :
    run (table continuation) ⟨left,scratch w (mark suffix),some 1⟩ (2*w.length+3) =
      ⟨2*push left w,2*(suffix/4),some 4⟩ := by
  induction w generalizing left with
  | nil => simpa [scratch,mark,push] using terminator continuation left (suffix/4)
  | cons b bs ih =>
    have ht : 2*(b::bs).length+3 = 2+(2*bs.length+3) := by simp; omega
    rw [ht,Source284ScratchScanner.run_add]
    change run (table continuation)
      (run (table continuation) ⟨left,bit b+4*scratch bs (mark suffix),some 1⟩ 2) _ = _
    rw [payload_pair,ih]
    rfl

/-- The actual finite table flips the payload, seeds the ignored suffix, and
returns to the original head. The old suffix is divided by eight. -/
theorem seed_scratch (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate suffix : Nat) :
    run (table continuation) ⟨certificate,2*scratch w (mark suffix),some 0⟩ (4*w.length+14) =
      ⟨certificate,2*flipped w (counter 0 ((suffix/4)/2)),some 16⟩ := by
  have ht : 4*w.length+14 = 1+((2*w.length+3)+(4+(1+(2*w.length+5)))) := by omega
  rw [ht,Source284ScratchScanner.run_add]
  change run (table continuation) (step (table continuation)
    ⟨certificate,2*scratch w (mark suffix),some 0⟩) _ = _
  rw [initial,Source284ScratchScanner.run_add,scan]
  change run (table continuation) (shiftConfig 4
    ⟨2*push (2*certificate) w,2*(suffix/4),some 0⟩) _ = _
  rw [relocated_run,Source284ScratchScanner.run_add,Source284CounterSeed.seed]
  change shiftConfig 4 (run (Source284CounterSeed.table (afterSeed continuation))
    (shiftConfig 2 (shiftConfig 3 ⟨2*push (2*certificate) w,2*counter 0 ((suffix/4)/2),some 0⟩)) _) = _
  rw [Source284CounterSeed.relocated_run]
  change shiftConfig 4 (shiftConfig 2 (run (Source284OrientationHandoff.table 0 (afterSeed continuation))
    (shiftConfig 3 ⟨2*push (2*certificate) w,2*counter 0 ((suffix/4)/2),some 0⟩) _)) = _
  rw [Source284OrientationHandoff.relocated_run]
  rw [Source284ScratchScanner.run_add]
  change shiftConfig 4 (shiftConfig 2 (shiftConfig 3 (run (afterSeed continuation)
    (step (afterSeed continuation) ⟨2*push (2*certificate) w,2*counter 0 ((suffix/4)/2),some 0⟩) _))) = _
  have hstep : step (afterSeed continuation)
      ⟨2*push (2*certificate) w,2*counter 0 ((suffix/4)/2),some 0⟩ =
      shiftConfig 1 ⟨4*push (2*certificate) w,counter 0 ((suffix/4)/2),some 0⟩ := by
    simp [step,afterSeed,shiftConfig,bit,Nat.testBit_zero]
    omega
  rw [hstep,after_relocated_run,Source284ScratchFlipReturn.return_frame]
  rfl


theorem shift_nested (c : Config) :
    shiftConfig 4 (shiftConfig 2 (shiftConfig 3 (shiftConfig 1 (shiftConfig 6 c)))) = shiftConfig 16 c := by
  cases c with
  | mk left right state => cases state <;> simp [shiftConfig] <;> omega

theorem continuation_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 16 c) fuel = shiftConfig 16 (run continuation c fuel) := by
  rw [← shift_nested c]
  rw [relocated_run,Source284CounterSeed.relocated_run,Source284OrientationHandoff.relocated_run,
    after_relocated_run,Source284ScratchFlipReturn.relocated_run,shift_nested]

theorem seed_scratch_then (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate suffix fuel : Nat) :
    run (table continuation) ⟨certificate,2*scratch w (mark suffix),some 0⟩ (4*w.length+14+fuel) =
      shiftConfig 16 (run continuation
        ⟨certificate,2*flipped w (counter 0 ((suffix/4)/2)),some 0⟩ fuel) := by
  rw [Source284ScratchScanner.run_add,seed_scratch]
  change run (table continuation)
    (shiftConfig 16 ⟨certificate,2*flipped w (counter 0 ((suffix/4)/2)),some 0⟩) fuel = _
  exact continuation_run continuation _ fuel

/-- The numeric source performs the scratch scan, counter seed, return,
and all requested continuation steps in one finite execution. -/
theorem source_seed_scratch (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (16+states) (table continuation) 1)
      (Source284Relative.initial (2*scratch w (mark suffix)) certificate) (4*w.length+14+fuel) =
      Source284SourceRelocation.lift 16
        (Source284Relative.run (encode states continuation 1)
          ⟨certificate,2*flipped w (counter 0 ((suffix/4)/2)),active 0⟩ fuel) := by
  let start : Config := ⟨certificate,2*scratch w (mark suffix),some 0⟩
  have hi : Valid (16+states) start := by intro q hq; simp [start] at hq; subst q; omega
  have hr := run_toSource (16+states) (table continuation) 1 start (closed states continuation hn hv)
    hi (4*w.length+14+fuel)
  rw [seed_scratch_then,← Source284SourceRelocation.lift_toSource] at hr
  let finish : Config := ⟨certificate,2*flipped w (counter 0 ((suffix/4)/2)),some 0⟩
  have hf : Valid states finish := by intro q hq; simp [finish] at hq; subst q; exact hn
  have hs := run_toSource states continuation 1 finish hv hf fuel
  rw [← hs] at hr
  exact hr

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284ScratchPack.description (16+states) (table continuation)

def totalCost (n : Nat) : Nat := Source284ScratchPack.totalCost n+(4*n+14)

theorem totalCost_formula (n : Nat) : totalCost n = 2*n*n+22*n+30 := by
  rw [totalCost,Source284ScratchPack.totalCost_formula]
  ring

/-- The counter seed runs in the same source table as the scratch packer,
from the packer's actual intermediate state. -/
theorem source_after_pack (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      ⟨certificate,2*scratch w (mark suffix),active 133⟩ (4*w.length+14) =
      ⟨certificate,2*flipped w (counter 0 ((suffix/4)/2)),active 149⟩ := by
  let c : Config := ⟨certificate,2*scratch w (mark suffix),some 0⟩
  have hc := closed states continuation hn hv
  have hvalid : Valid (133+(16+states))
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 c))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := run_toSource (133+(16+states)) (Source284ScratchPack.table (table continuation)) 1
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 c)))))
    (Source284ScratchPack.closed (16+states) (table continuation) (by omega) hc)
    hvalid (4*w.length+14)
  change Source284Relative.run (description states continuation)
    ⟨certificate,2*scratch w (mark suffix),active (8+(8+(16+(32+69))))⟩ _ = _ at hr
  have hs : 8+(8+(16+(32+69))) = 133 := by omega
  rw [hs] at hr
  rw [hr]
  change toSource (run (Source284InputSentinel.table
    (Source284ModePrefixScan.table (Source284ScratchTerminator.table
      (Source284PayloadLoop.table (table continuation)))))
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 c))))) _) = _
  rw [Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,
    Source284ScratchTerminator.relocated_run,Source284ModePrefixReturn.relocated_run,
    Source284PayloadLoop.relocated_run,seed_scratch]
  rfl

/-- Starting with a raw framed input and arbitrary certificate and high suffix,
the finite source packs the payload and seeds the counter in polynomial time. -/
theorem source_pack_seed (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) (totalCost w.length) =
      ⟨certificate,2*flipped w (counter 0 ((suffix/4)/2)),active 149⟩ := by
  have hc := closed states continuation hn hv
  have hp := Source284ScratchPack.source_pack_frame (16+states) (table continuation)
    w certificate suffix (by omega) hc
  change Source284Relative.run (description states continuation)
    (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) _ = _ at hp
  rw [totalCost,Source284Relative.run_add_clock,hp]
  change Source284Relative.run (description states continuation)
    ⟨certificate,2*scratch w (mark suffix),active 133⟩ _ = _
  exact source_after_pack states continuation w certificate suffix hn hv

/-- Once the seed is installed, the same encoded table executes a closed
continuation with exactly the requested additional source steps. -/
theorem source_after_seed (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      ⟨certificate,2*flipped w (counter 0 ((suffix/4)/2)),active 149⟩ fuel =
      Source284SourceRelocation.lift 149
        (Source284Relative.run (encode states continuation 1)
          ⟨certificate,2*flipped w (counter 0 ((suffix/4)/2)),active 0⟩ fuel) := by
  let c : Config := ⟨certificate,2*flipped w (counter 0 ((suffix/4)/2)),some 0⟩
  have hc := closed states continuation hn hv
  have hvalid : Valid (133+(16+states))
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 (shiftConfig 16 c)))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := run_toSource (133+(16+states)) (Source284ScratchPack.table (table continuation)) 1
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 (shiftConfig 16 c))))))
    (Source284ScratchPack.closed (16+states) (table continuation) (by omega) hc) hvalid fuel
  change Source284Relative.run (description states continuation)
    ⟨certificate,2*flipped w (counter 0 ((suffix/4)/2)),active (8+(8+(16+(32+(69+16)))))⟩ _ = _ at hr
  have he : 8+(8+(16+(32+(69+16)))) = 149 := by omega
  rw [he] at hr
  have hf : Valid states c := by intro q hq; simp [c] at hq; subst q; exact hn
  have hr0 := run_toSource states continuation 1 c hv hf fuel
  change Source284Relative.run (encode states continuation 1)
    ⟨certificate,2*flipped w (counter 0 ((suffix/4)/2)),active 0⟩ fuel = _ at hr0
  rw [hr,hr0]
  change toSource (run (Source284InputSentinel.table
    (Source284ModePrefixScan.table (Source284ScratchTerminator.table
      (Source284PayloadLoop.table (table continuation)))))
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 (shiftConfig 16 c)))))) fuel) = _
  rw [Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,
    Source284ScratchTerminator.relocated_run,Source284ModePrefixReturn.relocated_run,
    Source284PayloadLoop.relocated_run,continuation_run]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  rw [← Source284SourceRelocation.lift_toSource]

/-- The original raw framed input reaches the seeded suffix, then executes
its supplied continuation with all runtime steps charged. -/
theorem source_pack_seed_then (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) (totalCost w.length+fuel) =
      Source284SourceRelocation.lift 149
        (Source284Relative.run (encode states continuation 1)
          ⟨certificate,2*flipped w (counter 0 ((suffix/4)/2)),active 0⟩ fuel) := by
  rw [Source284Relative.run_add_clock,source_pack_seed states continuation w certificate suffix hn hv]
  exact source_after_seed states continuation w certificate suffix fuel hn hv

/-- Every numeric raw input has a finite execution with the same fixed table;
its ignored suffix need not be finite in length relative to its parsed payload. -/
theorem source_total_progress (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix : Nat),
      Source284Parser.encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description states continuation)
        (Source284Relative.initial input certificate) (totalCost (Source284Parser.length input)) =
        ⟨certificate,2*flipped w (counter 0 ((suffix/4)/2)),active 149⟩ := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_⟩
  rw [hlen,← hw]
  exact source_pack_seed states continuation w certificate suffix hn hv

namespace Fixtures

def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
example : run (table loop) ⟨7,2*scratch [] (mark 37),some 0⟩ 14 =
    ⟨7,2*flipped [] (counter 0 4),some 16⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284ScratchCounterSeed
