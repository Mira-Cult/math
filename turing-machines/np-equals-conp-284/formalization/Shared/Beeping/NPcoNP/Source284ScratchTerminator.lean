import Shared.Beeping.NPcoNP.Source284PayloadLoop

/-! A finite source-table pass installs a two-bit `0,1` terminator in the
ignored suffix. It preserves the parsed frame and the complete certificate;
the remaining high suffix is unchanged. This is preparation for the
quadratic payload-to-scratch loop, not yet canonical pair packing. -/
namespace Shared.Beeping.NPcoNP.Source284ScratchTerminator

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284WitnessScanArithmetic (pushPairs)

def mark (suffix : Nat) : Nat := 4*(suffix/4)+2

theorem mark_low (suffix : Nat) : mark suffix % 4 = 2 := by simp [mark]
theorem mark_high (suffix : Nat) : mark suffix / 4 = suffix/4 := by simp [mark]; omega

/-- Four mode-preserving rows overwrite the two suffix cells with `0,1`,
return to the frame, and enter the existing reverse scanner after its turn. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q < 4 then ⟨false,false,some (q+4)⟩
  else if q < 8 then ⟨true,true,some (q+4)⟩
  else if q < 12 then ⟨false,false,some (q+4)⟩
  else if q < 16 then ⟨false,false,some (q+12)⟩
  else shiftRow 16 (Source284ModePrefixReturn.table continuation (q-16) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (16+(32+states)) (table continuation) := by
  have hc := Source284ModePrefixReturn.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases h0 : q < 4
  · simp [table,h0] at hnext; omega
  · by_cases h1 : q < 8
    · simp [table,h0,h1] at hnext; omega
    · by_cases h2 : q < 12
      · simp [table,h0,h1,h2] at hnext; omega
      · by_cases h3 : q < 16
        · simp [table,h0,h1,h2,h3] at hnext; omega
        · have ht : (shiftRow 16 (Source284ModePrefixReturn.table continuation (q-16) b)).next = some q' := by
            simpa [table,h0,h1,h2,h3] using hnext
          have hq0 : q-16 < 32+states := by omega
          cases he : (Source284ModePrefixReturn.table continuation (q-16) b).next with
          | none => simp [shiftRow,he] at ht
          | some r =>
            have h := hc (q-16) hq0 b r he
            simp [shiftRow,he] at ht
            subst q'
            omega

theorem run_add (t : Nat → Bool → Row) (c : Config) (a b : Nat) :
    run t c (a+b) = run t (run t c a) b := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
    change step t (run t c (a+b)) = step t (run t (run t c a) b)
    rw [ih]

/-- Two arbitrary suffix bits are replaced by the terminator. The next
configuration is the reverse scanner immediately after its delimiter. -/
theorem write_mark (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (left suffix : Nat) :
    run (table continuation) ⟨2*left,suffix,some mode⟩ 4 =
      shiftConfig 16 ⟨2*mark suffix,left,some (8+mode)⟩ := by
  interval_cases mode <;>
    simp [run,step,table,bit,shiftConfig,mark,Nat.testBit_zero,Nat.div_div_eq_div_mul] <;>
    try split_ifs
  all_goals repeat' constructor
  all_goals omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (16+q) b = shiftRow 16 (Source284ModePrefixReturn.table continuation q b) := by
  have h4 : ¬ 16+q < 4 := by omega
  have h8 : ¬ 16+q < 8 := by omega
  have h12 : ¬ 16+q < 12 := by omega
  have h16 : ¬ 16+q < 16 := by omega
  simp [table,h4,h8,h12,h16]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 16 c) =
      shiftConfig 16 (step (Source284ModePrefixReturn.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (table continuation) (shiftConfig 16 c) clock =
      shiftConfig 16 (run (Source284ModePrefixReturn.table continuation) c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp only [run,ih,relocated_step]

/-- The saved certificate bits and the entire input frame are restored;
only the two ignored suffix cells are changed. -/
theorem mark_return (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (w : List Bool) (higher suffix : Nat) :
    run (table continuation) ⟨2*pushPairs (4*higher) w,suffix,some mode⟩ (2*w.length+9) =
      ⟨4*higher+mode,encodeFrame w (mark suffix),some 48⟩ := by
  have ht : 2*w.length+9 = 4+(2*w.length+5) := by omega
  rw [ht,run_add,write_mark _ _ hm,relocated_run,Source284PayloadPop.rest _ _ hm]
  rfl

/-- The actual source table first prepares the certificate boundary, scans
the frame, installs the scratch terminator, and restores the input frame. -/
theorem source_mark (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run
      (Source284InputSentinel.description (8+(16+(32+states)))
        (Source284ModePrefixScan.table (table continuation)))
      (Source284Relative.initial (encodeFrame w suffix) certificate) (4*w.length+14) =
      ⟨certificate,encodeFrame w (mark suffix),active 64⟩ := by
  have hm : certificate%4 < 4 := Nat.mod_lt certificate (by decide)
  have hc := closed states continuation hn hv
  have hcm := Source284ModePrefixScan.closed (16+(32+states)) (table continuation) (by omega) hc
  have hcs := Source284InputSentinel.closed (8+(16+(32+states)))
    (Source284ModePrefixScan.table (table continuation)) (by omega) hcm
  have hvalid : Valid (8+(8+(16+(32+states)))) ⟨certificate,encodeFrame w suffix,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    subst q
    omega
  have hr := run_toSource (8+(8+(16+(32+states))))
    (Source284InputSentinel.table (Source284ModePrefixScan.table (table continuation))) 1
    ⟨certificate,encodeFrame w suffix,some 0⟩ hcs hvalid (4*w.length+14)
  change Source284Relative.run
      (Source284InputSentinel.description (8+(16+(32+states)))
        (Source284ModePrefixScan.table (table continuation)))
      (Source284Relative.initial (encodeFrame w suffix) certificate) _ = _ at hr
  have ht : 4*w.length+14 = 4+((2*w.length+1)+(2*w.length+9)) := by omega
  rw [hr,ht,run_add,Source284InputSentinel.prepare]
  change toSource (run (Source284InputSentinel.table (Source284ModePrefixScan.table (table continuation)))
    (shiftConfig 8 ⟨4*(certificate/4),encodeFrame w suffix,some (certificate%4)⟩) _) = _
  rw [Source284InputSentinel.relocated_run,run_add,Source284ModePrefixScan.scan_frame _ _ hm]
  change toSource (shiftConfig 8 (run (Source284ModePrefixScan.table (table continuation))
    (shiftConfig 8 ⟨2*pushPairs (4*(certificate/4)) w,suffix,some (certificate%4)⟩) _)) = _
  rw [Source284ModePrefixScan.relocated_run,mark_return _ _ hm,
    Source284InputSentinel.certificate_recovered]
  rfl

/-- The marker overwrites only data after the first zero delimiter, so the
source parser sees exactly the same framed input. -/
theorem marked_parse (w : List Bool) (suffix : Nat) :
    Source284Parser.parse (encodeFrame w (mark suffix)) =
      Source284Parser.parse (encodeFrame w suffix) :=
  Source284Parser.parse_suffix_independent w _ _

end Shared.Beeping.NPcoNP.Source284ScratchTerminator
