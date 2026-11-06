import Shared.Beeping.NPcoNP.Source284ScratchFlipPipeline
import Shared.Beeping.NPcoNP.Source284Suffix

/-! A finite source-table conversion from the bidirectional scratch stream
`payload,1` to the source's `1,payload` frame with a high sentinel. It saves
one certificate bit in finite control and reuses the self-delimiting return.
This does not yet construct the canonical pair or bounded witness window. -/
set_option maxHeartbeats 2000000

namespace Shared.Beeping.NPcoNP.Source284ScratchNormalize

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284WitnessScanArithmetic (pushPairs)

/-- The leading zero and a temporarily cleared certificate bit form the
return boundary. Four modes are allocated; the actual entry uses mode 0 or 2. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some 1⟩
  else if q = 1 then ⟨false,true,some (2+bit b)⟩
  else if q < 4 then ⟨b,false,some (4+2*(q-2))⟩
  else if q < 8 then ⟨b,false,some (8+2*(q-4)+bit b)⟩
  else if q < 16 then
    if b then ⟨decide ((q-8)%2 = 1),true,some (16+(q-8))⟩
    else ⟨true,true,some (24+(q-8)/2)⟩
  else if q < 24 then ⟨true,true,some (32+(q-16)/2)⟩
  else if q < 28 then ⟨b,false,some (44+(q-24))⟩
  else if q < 32 then ⟨b,false,some q⟩
  else if q < 36 then ⟨b,false,some (4+(q-32))⟩
  else shiftRow 36 (Source284ModePrefixReturn.table continuation (q-36) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (36+(32+states)) (table continuation) := by
  have hc := Source284ModePrefixReturn.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases h0 : q = 0
  · subst q; simp [table] at hnext; omega
  · by_cases h1 : q = 1
    · subst q; cases b <;> simp [table,bit] at hnext <;> omega
    · by_cases h2 : q < 4
      · simp [table,h0,h1,h2] at hnext; omega
      · by_cases h3 : q < 8
        · cases b <;> simp [table,h0,h1,h2,h3,bit] at hnext <;> omega
        · by_cases h4 : q < 16
          · cases b <;> simp [table,h0,h1,h2,h3,h4] at hnext <;> omega
          · by_cases h5 : q < 24
            · simp [table,h0,h1,h2,h3,h4,h5] at hnext; omega
            · by_cases h6 : q < 28
              · simp [table,h0,h1,h2,h3,h4,h5,h6] at hnext; omega
              · by_cases h7 : q < 32
                · simp [table,h0,h1,h2,h3,h4,h5,h6,h7] at hnext; omega
                · by_cases h8 : q < 36
                  · simp [table,h0,h1,h2,h3,h4,h5,h6,h7,h8] at hnext; omega
                  · have ht : (shiftRow 36 (Source284ModePrefixReturn.table continuation (q-36) b)).next = some q' := by
                      simpa [table,h0,h1,h2,h3,h4,h5,h6,h7,h8] using hnext
                    have hq0 : q-36 < 32+states := by omega
                    cases he : (Source284ModePrefixReturn.table continuation (q-36) b).next with
                    | none => simp [shiftRow,he] at ht
                    | some r =>
                      have h := hc (q-36) hq0 b r he
                      simp [shiftRow,he] at ht
                      subst q'
                      omega

theorem setup (continuation : Nat → Bool → Row) (certificate input : Nat) :
    run (table continuation) ⟨certificate,2*input,some 0⟩ 3 =
      ⟨4*(certificate/2),input,some (4+2*(certificate%2))⟩ := by
  have hmod := Nat.mod_lt certificate (by decide : 0 < 2)
  by_cases hc : certificate % 2 = 1 <;>
    simp [run,step,table,bit,Nat.testBit_zero,hc] <;>
    omega

theorem pair_step1 (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left tail : Nat) (b : Bool) :
    step (table continuation) ⟨left,bit b+2+4*tail,some (4+mode)⟩ =
      ⟨2*left+bit b,1+2*tail,some (8+2*mode+bit b)⟩ := by
  interval_cases mode <;> cases b <;>
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem pair_step2 (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left tail : Nat) (b : Bool) :
    step (table continuation) ⟨2*left+bit b,1+2*tail,some (8+2*mode+bit b)⟩ =
      ⟨2*tail+bit b,2*left+bit b,some (16+2*mode+bit b)⟩ := by
  interval_cases mode <;> cases b <;>
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem pair_step3 (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left tail : Nat) (b : Bool) :
    step (table continuation) ⟨2*tail+bit b,2*left+bit b,some (16+2*mode+bit b)⟩ =
      ⟨2*left+1,2*tail+bit b,some (32+mode)⟩ := by
  interval_cases mode <;> cases b <;>
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem pair_step4 (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left tail : Nat) (b : Bool) :
    step (table continuation) ⟨2*left+1,2*tail+bit b,some (32+mode)⟩ =
      ⟨4*left+2+bit b,tail,some (4+mode)⟩ := by
  interval_cases mode <;> cases b <;>
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem convert_pair (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left tail : Nat) (b : Bool) :
    run (table continuation) ⟨left,bit b+2+4*tail,some (4+mode)⟩ 4 =
      ⟨4*left+2+bit b,tail,some (4+mode)⟩ := by
  rw [Source284HardwireTable.run_front, pair_step1 _ _ hm,
    Source284HardwireTable.run_front, pair_step2 _ _ hm,
    Source284HardwireTable.run_front, pair_step3 _ _ hm,
    Source284HardwireTable.run_front, pair_step4 _ _ hm]
  rfl

theorem convert_pairs (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (w : List Bool) (left tail : Nat) :
    run (table continuation) ⟨left,flipped w tail,some (4+mode)⟩ (4*w.length) =
      ⟨pushPairs left w,4*tail,some (4+mode)⟩ := by
  induction w generalizing left with
  | nil => rfl
  | cons b bs ih =>
    have ht : 4*(b::bs).length = 4+4*bs.length := by simp; omega
    rw [ht,Source284PayloadPop.run_add]
    change run (table continuation)
      (run (table continuation) ⟨left,bit b+2+4*flipped bs tail,some (4+mode)⟩ 4) _ = _
    rw [convert_pair _ _ hm,ih]
    cases b <;> simp [pushPairs,bit]

/-- Convert `00` to the source frame's delimiter/sentinel `01`, turn back,
then hand off just after the delimiter to the existing reverse scanner. -/
theorem finish_step1 (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left tail : Nat) :
    step (table continuation) ⟨left,4*tail,some (4+mode)⟩ =
      ⟨2*left,2*tail,some (8+2*mode)⟩ := by
  interval_cases mode <;> simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega

theorem finish_step2 (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left tail : Nat) :
    step (table continuation) ⟨2*left,2*tail,some (8+2*mode)⟩ =
      ⟨2*tail+1,2*left,some (24+mode)⟩ := by
  interval_cases mode <;> simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega

theorem finish_step3 (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left tail : Nat) :
    step (table continuation) ⟨2*tail+1,2*left,some (24+mode)⟩ =
      shiftConfig 36 ⟨2*(2*tail+1),left,some (8+mode)⟩ := by
  interval_cases mode <;> simp [step,table,bit,shiftConfig,Nat.testBit_zero,Nat.mul_mod] <;> omega

theorem finish_scan (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left tail : Nat) :
    run (table continuation) ⟨left,4*tail,some (4+mode)⟩ 3 =
      shiftConfig 36 ⟨2*(2*tail+1),left,some (8+mode)⟩ := by
  rw [Source284HardwireTable.run_front,finish_step1 _ _ hm,
    Source284HardwireTable.run_front,finish_step2 _ _ hm,
    Source284HardwireTable.run_front,finish_step3 _ _ hm]
  rfl

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (36+q) b = shiftRow 36 (Source284ModePrefixReturn.table continuation q b) := by
  have h0 : 36+q ≠ 0 := by omega
  have h1 : 36+q ≠ 1 := by omega
  have h4 : ¬ 36+q < 4 := by omega
  have h8 : ¬ 36+q < 8 := by omega
  have h16 : ¬ 36+q < 16 := by omega
  have h24 : ¬ 36+q < 24 := by omega
  have h28 : ¬ 36+q < 28 := by omega
  have h32 : ¬ 36+q < 32 := by omega
  have h36 : ¬ 36+q < 36 := by omega
  simp [table,h0,h1,h4,h8,h16,h24,h28,h32,h36]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 36 c) =
      shiftConfig 36 (step (Source284ModePrefixReturn.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (table continuation) (shiftConfig 36 c) clock =
      shiftConfig 36 (run (Source284ModePrefixReturn.table continuation) c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp only [run,ih,relocated_step]

/-- A fixed finite table converts every scratch payload in linear source time.
The extra zero on the certificate side is the original scratch boundary. -/
theorem normalize (continuation : Nat → Bool → Row) (w : List Bool) (certificate tail : Nat) :
    run (table continuation) ⟨certificate,2*flipped w tail,some 0⟩ (6*w.length+11) =
      ⟨2*certificate,encodeFrame w (2*tail+1),some 68⟩ := by
  have hm : 2*(certificate%2) < 4 := by have h := Nat.mod_lt certificate (by decide : 0 < 2); omega
  have ht : 6*w.length+11 = 3+(4*w.length+(3+(2*w.length+5))) := by omega
  rw [ht,Source284PayloadPop.run_add _ _ 3 (4*w.length+(3+(2*w.length+5))),setup]
  rw [Source284PayloadPop.run_add _ _ (4*w.length) (3+(2*w.length+5)),convert_pairs _ _ hm]
  rw [Source284PayloadPop.run_add _ _ 3 (2*w.length+5),finish_scan _ _ hm,relocated_run,
    Source284PayloadPop.rest _ _ hm]
  have hc : 4*(certificate/2)+2*(certificate%2) = 2*certificate := by omega
  simp [shiftConfig,hc]

/-- Higher retained tape data starts strictly after the complete source frame
and its sentinel. It is not asserted to have been erased. -/
theorem normalized_suffix (w : List Bool) (tail : Nat) :
    encodeFrame w (2*tail+1) = encodeFrame w 1 + 4^(w.length+1)*tail := by
  rw [Source284Parser.encodeFrame_decompose, Source284Parser.encodeFrame_decompose, pow_succ]
  ring

end Shared.Beeping.NPcoNP.Source284ScratchNormalize
