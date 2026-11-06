import Shared.Beeping.NPcoNP.Source284ModePrefixReturn

/-! A finite source-table copy operation. It scans the framed input, remembers
its last payload bit in finite control, writes that bit into the first ignored
suffix cell, then uses the self-delimiting return to restore the input prefix
and certificate. It copies one bit only; it is not a complete packed loader. -/
namespace Shared.Beeping.NPcoNP.Source284LastPayloadCopy

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284WitnessScanArithmetic (pushPairs)

def lastOr (default : Bool) : List Bool → Bool
  | [] => default
  | b :: bs => lastOr b bs

def replaceLow (suffix : Nat) (b : Bool) : Nat := 2*(suffix/2)+bit b

theorem lastOr_snoc (default : Bool) (xs : List Bool) (b : Bool) :
    lastOr default (xs ++ [b]) = b := by
  induction xs generalizing default with
  | nil => rfl
  | cons a xs ih => simpa [lastOr] using ih a

/-- Eight marker modes store the two certificate bits and a payload bit;
eight payload modes update the stored payload bit. Eight boundary rows write
that bit while turning into the existing finite return routine. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q < 8 then ⟨b,false,some (if b then 8+q else 16+q)⟩
  else if q < 16 then ⟨b,false,some ((q-8)%4+4*bit b)⟩
  else if q < 24 then ⟨decide ((q-16)/4 = 1),true,some (28+(q-16)%4)⟩
  else shiftRow 24 (Source284ModePrefixReturn.table continuation (q-24) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (24+(32+states)) (table continuation) := by
  have hc := Source284ModePrefixReturn.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases h0 : q < 8
  · cases b <;> simp [table,h0] at hnext <;> omega
  · by_cases h1 : q < 16
    · cases b <;> simp [table,h0,h1,bit] at hnext <;> omega
    · by_cases h2 : q < 24
      · simp [table,h0,h1,h2] at hnext
        have hm := Nat.mod_lt (q-16) (by decide : 0 < 4)
        omega
      · have ht : (shiftRow 24 (Source284ModePrefixReturn.table continuation (q-24) b)).next = some q' := by
          simpa [table,h0,h1,h2] using hnext
        have hq0 : q-24 < 32+states := by omega
        cases he : (Source284ModePrefixReturn.table continuation (q-24) b).next with
        | none => simp [shiftRow,he] at ht
        | some r =>
          have h := hc (q-24) hq0 b r he
          simp [shiftRow,he] at ht
          subst q'
          omega

theorem marker_row (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (last b : Bool) :
    table continuation (mode+4*bit last) b =
      ⟨b,false,some (if b then 8+(mode+4*bit last) else 16+(mode+4*bit last))⟩ := by
  cases last <;> simp [table,bit] <;> omega

theorem payload_row (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (last b : Bool) :
    table continuation (8+(mode+4*bit last)) b =
      ⟨b,false,some (mode+4*bit b)⟩ := by
  interval_cases mode <;> cases last <;> cases b <;> simp [table,bit]

theorem marker_step (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (last : Bool) (left right : Nat) :
    step (table continuation) ⟨left,right,some (mode+4*bit last)⟩ =
      ⟨2*left+right%2,right/2,
        some (if right.testBit 0 then 8+(mode+4*bit last) else 16+(mode+4*bit last))⟩ := by
  simp [step,marker_row _ _ hm,Nat.testBit_zero,Source284WitnessScanner.bit_decide_mod]

theorem payload_step (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (last : Bool) (left right : Nat) :
    step (table continuation) ⟨left,right,some (8+(mode+4*bit last))⟩ =
      ⟨2*left+right%2,right/2,some (mode+4*bit (right.testBit 0))⟩ := by
  simp [step,payload_row _ _ hm,Nat.testBit_zero,Source284WitnessScanner.bit_decide_mod]

theorem run_add (t : Nat → Bool → Row) (c : Config) (a b : Nat) :
    run t c (a+b) = run t (run t c a) b := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
    change step t (run t c (a+b)) = step t (run t (run t c a) b)
    rw [ih]

theorem marker_payload (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (last : Bool) (left suffix : Nat) (b : Bool) (rest : List Bool) :
    run (table continuation) ⟨left,encodeFrame (b::rest) suffix,some (mode+4*bit last)⟩ 2 =
      ⟨4*left+2+(if b then 1 else 0),encodeFrame rest suffix,some (mode+4*bit b)⟩ := by
  interval_cases mode <;> cases last <;> cases b <;>
    simp [run,step,table,encodeFrame,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod,bit] <;>
    congr 1 <;> split_ifs <;> omega

/-- The last payload bit is carried in control; an empty frame retains the
specified initial bit. No suffix bits have been modified yet. -/
theorem scan_frame (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (last : Bool) (w : List Bool) (left suffix : Nat) :
    run (table continuation) ⟨left,encodeFrame w suffix,some (mode+4*bit last)⟩ (2*w.length+1) =
      ⟨2*pushPairs left w,suffix,some (16+(mode+4*bit (lastOr last w)))⟩ := by
  induction w generalizing left last with
  | nil => simp [run,marker_step _ _ hm,encodeFrame,pushPairs,lastOr,Nat.testBit_zero]
  | cons b bs ih =>
    have ht : 2*(b::bs).length+1 = 2+(2*bs.length+1) := by simp; omega
    rw [ht,run_add,marker_payload _ _ hm]
    simpa [pushPairs,lastOr] using ih b (4*left+2+(if b then 1 else 0))

theorem write_and_turn (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (last : Bool) (left suffix : Nat) :
    step (table continuation) ⟨left,suffix,some (16+(mode+4*bit last))⟩ =
      ⟨replaceLow suffix last,left,some (24+(4+mode))⟩ := by
  interval_cases mode <;> cases last <;>
    simp [step,table,bit,replaceLow,Nat.testBit_zero] <;> omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (24+q) b = shiftRow 24 (Source284ModePrefixReturn.table continuation q b) := by
  have h8 : ¬ 24+q < 8 := by omega
  have h16 : ¬ 24+q < 16 := by omega
  have h24 : ¬ 24+q < 24 := by omega
  simp [table,h8,h16,h24]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 24 c) =
      shiftConfig 24 (step (Source284ModePrefixReturn.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (table continuation) (shiftConfig 24 c) clock =
      shiftConfig 24 (run (Source284ModePrefixReturn.table continuation) c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp only [run,ih,relocated_step]

theorem return_turn (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left right : Nat) :
    step (Source284ModePrefixReturn.table continuation) ⟨left,right,some mode⟩ =
      ⟨right,left,some (4+mode)⟩ := by
  interval_cases mode <;>
    simp [step,Source284ModePrefixReturn.table,bit,Nat.testBit_zero] <;>
    congr 1 <;> split_ifs <;> omega

/-- The existing return starts with a turn; the copy table substitutes its
own write-and-turn transition and then runs the remaining return steps. -/
theorem return_after_turn (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (w : List Bool) (higher suffix : Nat) :
    run (Source284ModePrefixReturn.table continuation)
      ⟨suffix,2*pushPairs (4*higher) w,some (4+mode)⟩ (2*w.length+6) =
      ⟨4*higher+mode,encodeFrame w suffix,some 32⟩ := by
  have h := Source284ModePrefixReturn.return_frame continuation mode hm w higher suffix
  have ht : 2*w.length+7 = (2*w.length+6)+1 := by omega
  rw [ht,Source284HardwireTable.run_front,return_turn _ _ hm] at h
  exact h

/-- A single finite table copies the last payload bit into the low ignored
suffix cell and returns to the original frame boundary. The certificate is
restored in full. The empty frame copies the fixed bit zero. -/
theorem copy_and_return (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (w : List Bool) (higher suffix : Nat) :
    run (table continuation) ⟨4*higher,encodeFrame w suffix,some mode⟩ (4*w.length+8) =
      ⟨4*higher+mode,encodeFrame w (replaceLow suffix (lastOr false w)),some 56⟩ := by
  have ht : 4*w.length+8 = (2*w.length+1)+((2*w.length+6)+1) := by omega
  rw [ht,run_add]
  have hs := scan_frame continuation mode hm false w (4*higher) suffix
  have hstart : mode+4*bit false = mode := by simp [bit]
  rw [hstart] at hs
  rw [hs,Source284HardwireTable.run_front,write_and_turn _ _ hm]
  change run (table continuation)
    (shiftConfig 24 ⟨replaceLow suffix (lastOr false w),2*pushPairs (4*higher) w,some (4+mode)⟩) _ = _
  rw [relocated_run,return_after_turn _ _ hm]
  rfl

theorem replaceLow_bit (suffix : Nat) (b : Bool) : replaceLow suffix b % 2 = bit b := by
  cases b <;> simp [replaceLow,bit]

theorem replaceLow_high (suffix : Nat) (b : Bool) : replaceLow suffix b / 2 = suffix/2 := by
  cases b <;> simp [replaceLow,bit] <;> omega

/-- The source parser sees the same public frame despite the scratch write. -/
theorem copy_parse (w : List Bool) (suffix : Nat) (b : Bool) :
    Source284Parser.parse (encodeFrame w (replaceLow suffix b)) =
      Source284Parser.parse (encodeFrame w suffix) :=
  Source284Parser.parse_suffix_independent w _ _

/-- The composed, actually encoded source program starts from both raw tape
halves and performs the copy in exactly `4*n+12` source steps. -/
theorem source_copy (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (Source284InputSentinel.description (24+(32+states)) (table continuation))
      (Source284Relative.initial (encodeFrame w suffix) certificate) (4*w.length+12) =
      ⟨certificate,encodeFrame w (replaceLow suffix (lastOr false w)),active 64⟩ := by
  have hc := closed states continuation hn hv
  have hcs := Source284InputSentinel.closed (24+(32+states)) (table continuation) (by omega) hc
  have hvalid : Valid (8+(24+(32+states))) ⟨certificate,encodeFrame w suffix,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    subst q
    omega
  have hr := run_toSource (8+(24+(32+states))) (Source284InputSentinel.table (table continuation)) 1
    ⟨certificate,encodeFrame w suffix,some 0⟩ hcs hvalid (4*w.length+12)
  change Source284Relative.run (Source284InputSentinel.description (24+(32+states)) (table continuation))
    (Source284Relative.initial (encodeFrame w suffix) certificate) _ = _ at hr
  have ht : 4*w.length+12 = 4+(4*w.length+8) := by omega
  rw [hr,ht,run_add,Source284InputSentinel.prepare]
  have hm : certificate%4 < 4 := Nat.mod_lt certificate (by decide)
  change toSource (run (Source284InputSentinel.table (table continuation))
    (shiftConfig 8 ⟨4*(certificate/4),encodeFrame w suffix,some (certificate%4)⟩) _) = _
  rw [Source284InputSentinel.relocated_run,copy_and_return _ _ hm,
    Source284InputSentinel.certificate_recovered]
  rfl

/-- For a nonempty payload the bit written to the first ignored suffix
position is exactly its final payload bit. -/
theorem source_copy_snoc (states : Nat) (continuation : Nat → Bool → Row)
    (xs : List Bool) (b : Bool) (certificate suffix : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (Source284InputSentinel.description (24+(32+states)) (table continuation))
      (Source284Relative.initial (encodeFrame (xs++[b]) suffix) certificate)
      (4*(xs++[b]).length+12) =
      ⟨certificate,encodeFrame (xs++[b]) (replaceLow suffix b),active 64⟩ := by
  simpa [lastOr_snoc] using source_copy states continuation (xs++[b]) certificate suffix hn hv

/-- Every raw numeric input reaches the boundary after a finite cost fixed
by its parsed length. The existential frame decomposition is not runtime data. -/
theorem source_total_progress (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (Source284InputSentinel.description (24+(32+states)) (table continuation))
        (Source284Relative.initial input certificate) (4*Source284Parser.length input+12) =
      ⟨certificate,encodeFrame w (replaceLow suffix (lastOr false w)),active 64⟩ := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_⟩
  rw [hlen,← hw]
  exact source_copy states continuation w certificate suffix hn hv

/-- The linked continuation starts on the copied tape in the same source
execution, with no free initialization or hidden steps. -/
theorem source_after_copy (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix clock : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.accepts (Source284InputSentinel.description (24+(32+states)) (table continuation))
      (encodeFrame w suffix) certificate (4*w.length+12+clock) =
    Source284Relative.accepts (encode states continuation 1)
      (encodeFrame w (replaceLow suffix (lastOr false w))) certificate clock := by
  let newInput := encodeFrame w (replaceLow suffix (lastOr false w))
  let c : Config := ⟨certificate,newInput,some 0⟩
  have h0 : Valid states c := by
    intro q hq
    simp [c] at hq
    subst q
    exact hn
  have h1 : Valid (8+(24+(32+states))) (shiftConfig 8 (shiftConfig 24 (shiftConfig 32 c))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hc := closed states continuation hn hv
  have hcs := Source284InputSentinel.closed (24+(32+states)) (table continuation) (by omega) hc
  have hr1 := run_toSource (8+(24+(32+states))) (Source284InputSentinel.table (table continuation)) 1
    (shiftConfig 8 (shiftConfig 24 (shiftConfig 32 c))) hcs h1 clock
  have hr0 := run_toSource states continuation 1 c hv h0 clock
  change Source284Relative.run (Source284InputSentinel.description (24+(32+states)) (table continuation))
    ⟨certificate,newInput,active (8+(24+32))⟩ clock = _ at hr1
  have hs : 8+(24+32) = 64 := by omega
  rw [hs] at hr1
  change Source284Relative.run (encode states continuation 1)
    (Source284Relative.initial newInput certificate) clock = _ at hr0
  unfold Source284Relative.accepts
  rw [Source284Relative.run_add_clock,source_copy states continuation w certificate suffix hn hv,
    hr1,hr0,Source284InputSentinel.relocated_run,relocated_run,Source284ModePrefixReturn.relocated_run]
  cases h : (run continuation c clock).state <;>
    simp [toSource,shiftConfig,nextState,h,active]

example : lastOr false [true,false,true] = true := rfl
example : replaceLow 19 false = 18 := rfl
example : replaceLow 18 true = 19 := rfl

end Shared.Beeping.NPcoNP.Source284LastPayloadCopy
