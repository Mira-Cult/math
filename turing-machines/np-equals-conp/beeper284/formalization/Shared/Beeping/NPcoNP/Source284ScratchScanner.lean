import Shared.Beeping.NPcoNP.Source284ScratchPack
import Shared.Beeping.NPcoNP.Source284TransferInvolution

/-! A finite source-table scanner for the self-delimited payload scratch
stream. It reads the initial zero, then payload/zero pairs, and exits on the
`0,1` terminator. The table moves the scanned bits across the head without
altering them. It does not yet build a canonical pair or parse certificates. -/
namespace Shared.Beeping.NPcoNP.Source284ScratchScanner

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284PayloadLoop (scratch)
open Shared.Beeping.NPcoNP.Source284ScratchTerminator (mark)

/-- Three prefix states, followed by a finite continuation. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some 1⟩
  else if q = 1 then ⟨b,false,some 2⟩
  else if q = 2 then ⟨b,false,some (if b then 3 else 1)⟩
  else shiftRow 3 (continuation (q-3) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (3+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases h0 : q = 0
  · subst q; simp [table] at hnext; omega
  · by_cases h1 : q = 1
    · subst q; simp [table] at hnext; omega
    · by_cases h2 : q = 2
      · subst q; cases b <;> simp [table] at hnext <;> omega
      · have ht : (shiftRow 3 (continuation (q-3) b)).next = some q' := by
          simpa [table,h0,h1,h2] using hnext
        have hq0 : q-3 < states := by omega
        cases he : (continuation (q-3) b).next with
        | none => simp [shiftRow,he] at ht
        | some r =>
          have h := hv (q-3) hq0 b r he
          simp [shiftRow,he] at ht
          subst q'
          omega

/-- Append payload/zero pairs to the scanned side of the head. -/
def push : Nat → List Bool → Nat
  | left, [] => left
  | left, b::bs => push (4*left+2*bit b) bs

theorem run_add (t : Nat → Bool → Row) (c : Config) (a b : Nat) :
    run t c (a+b) = run t (run t c a) b := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
    change step t (run t c (a+b)) = step t (run t (run t c a) b)
    rw [ih]

theorem initial (continuation : Nat → Bool → Row) (left right : Nat) :
    step (table continuation) ⟨left,2*right,some 0⟩ = ⟨2*left,right,some 1⟩ := by
  simp [step,table,bit,Nat.testBit_zero]

theorem payload_pair (continuation : Nat → Bool → Row) (left tail : Nat) (b : Bool) :
    run (table continuation) ⟨left,bit b+4*tail,some 1⟩ 2 =
      ⟨4*left+2*bit b,tail,some 1⟩ := by
  cases b <;> simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;>
    congr 1 <;> try split_ifs <;> omega

theorem terminator (continuation : Nat → Bool → Row) (left tail : Nat) :
    run (table continuation) ⟨left,4*tail+2,some 1⟩ 2 =
      ⟨4*left+1,tail,some 3⟩ := by
  simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;>
    congr 1 <;> try split_ifs <;> omega

theorem scan (continuation : Nat → Bool → Row) (w : List Bool) (left suffix : Nat) :
    run (table continuation) ⟨left,scratch w (mark suffix),some 1⟩ (2*w.length+2) =
      ⟨4*push left w+1,suffix/4,some 3⟩ := by
  induction w generalizing left with
  | nil => simpa [scratch,mark,push] using terminator continuation left (suffix/4)
  | cons b bs ih =>
    have ht : 2*(b::bs).length+2 = 2+(2*bs.length+2) := by simp; omega
    rw [ht,run_add]
    change run (table continuation)
      (run (table continuation) ⟨left,bit b+4*scratch bs (mark suffix),some 1⟩ 2) _ = _
    rw [payload_pair,ih]
    rfl

theorem scan_initial (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate suffix : Nat) :
    run (table continuation) ⟨certificate,2*scratch w (mark suffix),some 0⟩ (2*w.length+3) =
      ⟨4*push (2*certificate) w+1,suffix/4,some 3⟩ := by
  have ht : 2*w.length+3 = (2*w.length+2)+1 := by omega
  rw [ht,Source284HardwireTable.run_front,initial,scan]

/-- Starting at the produced scratch tape, the real finite source table
reaches the continuation after exactly two steps per payload bit plus three. -/
theorem source_scan (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (3+states) (table continuation) 1)
      (Source284Relative.initial (2*scratch w (mark suffix)) certificate) (2*w.length+3) =
      ⟨4*push (2*certificate) w+1,suffix/4,active 3⟩ := by
  have hvalid : Valid (3+states) ⟨certificate,2*scratch w (mark suffix),some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    subst q
    omega
  have hr := run_toSource (3+states) (table continuation) 1
    ⟨certificate,2*scratch w (mark suffix),some 0⟩ (closed states continuation hn hv) hvalid (2*w.length+3)
  change Source284Relative.run (encode (3+states) (table continuation) 1)
    (Source284Relative.initial (2*scratch w (mark suffix)) certificate) _ = _ at hr
  rw [hr,scan_initial]
  rfl

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (3+q) b = shiftRow 3 (continuation q b) := by
  have h0 : 3+q ≠ 0 := by omega
  have h1 : 3+q ≠ 1 := by omega
  have h2 : 3+q ≠ 2 := by omega
  simp [table,h0,h1,h2]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 3 c) = shiftConfig 3 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (table continuation) (shiftConfig 3 c) clock = shiftConfig 3 (run continuation c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp only [run,ih,relocated_step]

/-- The scanner starts in the very same encoded source program that built
the scratch stream; it needs no length or preloaded delimiter. -/
theorem source_after_pack (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (Source284ScratchPack.description (3+states) (table continuation))
      ⟨certificate,2*scratch w (mark suffix),active 133⟩ (2*w.length+3) =
      ⟨4*push (2*certificate) w+1,suffix/4,active 136⟩ := by
  let c : Config := ⟨certificate,2*scratch w (mark suffix),some 0⟩
  have hc := closed states continuation hn hv
  have hvalid : Valid (133+(3+states))
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 c))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := run_toSource (133+(3+states)) (Source284ScratchPack.table (table continuation)) 1
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 c)))))
    (Source284ScratchPack.closed (3+states) (table continuation) (by omega) hc)
    hvalid (2*w.length+3)
  change Source284Relative.run (Source284ScratchPack.description (3+states) (table continuation))
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
    Source284PayloadLoop.relocated_run,scan_initial]
  rfl

/-- The actual source table packs and then scans the payload in one finite
execution, with all startup and scan steps included. -/
theorem source_pack_and_scan (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (Source284ScratchPack.description (3+states) (table continuation))
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate)
      (Source284ScratchPack.totalCost w.length+(2*w.length+3)) =
      ⟨4*push (2*certificate) w+1,suffix/4,active 136⟩ := by
  have hc := closed states continuation hn hv
  have hp := Source284ScratchPack.source_pack_frame (3+states) (table continuation)
    w certificate suffix (by omega) hc
  change Source284Relative.run (Source284ScratchPack.description (3+states) (table continuation))
    (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) _ = _ at hp
  rw [Source284Relative.run_add_clock,hp]
  change Source284Relative.run (Source284ScratchPack.description (3+states) (table continuation))
    ⟨certificate,2*scratch w (mark suffix),active 133⟩ _ = _
  exact source_after_pack states continuation w certificate suffix hn hv

/-- The complete pack-and-scan cost is a fixed quadratic in parsed input
length, including terminator setup and all scanner steps. -/
theorem total_cost (n : Nat) :
    Source284ScratchPack.totalCost n+(2*n+3) = 2*n*n+20*n+19 := by
  rw [Source284ScratchPack.totalCost_formula]
  ring

theorem record_count (states : Nat) (continuation : Nat → Bool → Row) :
    (records (133+(3+states)) (Source284ScratchPack.table (table continuation))).length =
      2*(136+states) := by
  simp [records]
  omega

/-- For every raw numeric input, the table reaches the scanner continuation;
the decomposition is used only in the proof. -/
theorem source_total_progress (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix : Nat),
      Source284Parser.encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (Source284ScratchPack.description (3+states) (table continuation))
        (Source284Relative.initial input certificate)
        (2*(Source284Parser.length input)*(Source284Parser.length input)+
          20*Source284Parser.length input+19) =
      ⟨4*push (2*certificate) w+1,suffix/4,active 136⟩ := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_⟩
  rw [hlen,← hw,← total_cost]
  exact source_pack_and_scan states continuation w certificate suffix hn hv

theorem transfer_pair (left tail : Nat) (b : Bool) :
    Source284LoaderAlgebra.transfer 2 left (bit b+4*tail) = (4*left+2*bit b,tail) := by
  cases b <;> simp [Source284LoaderAlgebra.transfer,bit] <;> congr 1 <;> omega

/-- The scanner is a literal bit transfer on the given valid scratch format. -/
theorem scan_transfer (w : List Bool) (left suffix : Nat) :
    Source284LoaderAlgebra.transfer (2*w.length+2) left (scratch w (mark suffix)) =
      (4*push left w+1,suffix/4) := by
  induction w generalizing left with
  | nil =>
    simp [scratch,mark,push,Source284LoaderAlgebra.transfer]
    congr 1 <;> omega
  | cons b bs ih =>
    have ht : 2*(b::bs).length+2 = 2+(2*bs.length+2) := by simp; omega
    rw [ht,Source284TransferInvolution.transfer_add]
    change (let p := Source284LoaderAlgebra.transfer 2 left (bit b+4*scratch bs (mark suffix));
      Source284LoaderAlgebra.transfer (2*bs.length+2) p.1 p.2) = _
    rw [transfer_pair]
    simp only [Prod.fst,Prod.snd,push]
    exact ih _

/-- Reversing the exact finite transfer recovers the scratch tape and the
complete certificate half; this arithmetic inverse is not a machine return. -/
theorem scanned_information (w : List Bool) (certificate suffix : Nat) :
    Source284LoaderAlgebra.transfer (2*w.length+3) (suffix/4)
      (4*push (2*certificate) w+1) = (2*scratch w (mark suffix),certificate) := by
  have hfirst : Source284LoaderAlgebra.transfer (2*w.length+3) certificate
      (2*scratch w (mark suffix)) = (4*push (2*certificate) w+1,suffix/4) := by
    have ht : 2*w.length+3 = (2*w.length+2)+1 := by omega
    rw [ht,Source284LoaderAlgebra.transfer]
    simpa using scan_transfer w (2*certificate) suffix
  have hinv := Source284TransferInvolution.transfer_involution (2*w.length+3) certificate
    (2*scratch w (mark suffix))
  rw [hfirst] at hinv
  exact hinv

/-- After packing and scanning, the finite continuation executes on the
actual resulting tape; its runtime is added to the setup and scan cost. -/
theorem source_after_pack_scan (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix clock : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.accepts (Source284ScratchPack.description (3+states) (table continuation))
      (Source284Parser.encodeFrame w suffix) certificate
      (Source284ScratchPack.totalCost w.length+(2*w.length+3)+clock) =
    Source284Relative.accepts (encode states continuation 1) (suffix/4)
      (4*push (2*certificate) w+1) clock := by
  let c : Config := ⟨4*push (2*certificate) w+1,suffix/4,some 0⟩
  have h0 : Valid states c := by
    intro q hq
    simp [c] at hq
    subst q
    exact hn
  have h1 : Valid (133+(3+states))
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 (shiftConfig 3 c)))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hc := closed states continuation hn hv
  have hr1 := run_toSource (133+(3+states)) (Source284ScratchPack.table (table continuation)) 1
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 (shiftConfig 3 c))))))
    (Source284ScratchPack.closed (3+states) (table continuation) (by omega) hc) h1 clock
  have hr0 := run_toSource states continuation 1 c hv h0 clock
  change Source284Relative.run (Source284ScratchPack.description (3+states) (table continuation))
    ⟨4*push (2*certificate) w+1,suffix/4,active (8+(8+(16+(32+(69+3)))))⟩ clock = _ at hr1
  have hs : 8+(8+(16+(32+(69+3)))) = 136 := by omega
  rw [hs] at hr1
  change Source284Relative.run (encode states continuation 1)
    (Source284Relative.initial (suffix/4) (4*push (2*certificate) w+1)) clock = _ at hr0
  unfold Source284Relative.accepts
  rw [Source284Relative.run_add_clock,source_pack_and_scan states continuation w certificate suffix hn hv,
    hr1,hr0]
  change ((toSource (run (Source284InputSentinel.table
    (Source284ModePrefixScan.table (Source284ScratchTerminator.table
      (Source284PayloadLoop.table (table continuation)))))
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 (shiftConfig 3 c)))))) clock)).state == 0) =
      ((toSource (run continuation c clock)).state == 0)
  rw [Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,
    Source284ScratchTerminator.relocated_run,Source284ModePrefixReturn.relocated_run,
    Source284PayloadLoop.relocated_run,relocated_run]
  cases h : (run continuation c clock).state <;>
    simp [toSource,shiftConfig,nextState,h,active]

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (Source284ScratchPack.description (3+states) (table continuation))
      (Source284Relative.initial 0 0) 19 = ⟨1,0,active 136⟩ := by
  simpa [Source284Parser.encodeFrame,Source284ScratchPack.totalCost,
    Source284PayloadLoop.cost,push] using
    source_pack_and_scan states continuation [] 0 0 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (Source284ScratchPack.description (3+states) (table continuation))
      (Source284Relative.initial 295 7) 67 = ⟨929,2,active 136⟩ := by
  simpa [Source284Parser.encodeFrame,Source284ScratchPack.totalCost,
    Source284PayloadLoop.cost,push,bit] using
    source_pack_and_scan states continuation [true,false] 7 9 hn hv

end Shared.Beeping.NPcoNP.Source284ScratchScanner
