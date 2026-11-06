import Shared.Beeping.NPcoNP.Source284PayloadPop

/-! The exact configuration immediately before the final source transition
of a payload-pop pass. This is needed to connect one pass back to the next;
the actual loop is not yet defined here. -/
namespace Shared.Beeping.NPcoNP.Source284PayloadPopPrecise

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284WitnessScanArithmetic (pushPairs)
open Shared.Beeping.NPcoNP.Source284TaggedWitnessRoundtrip (pushPairs_snoc rawPairs_frame)
open Shared.Beeping.NPcoNP.Source284PayloadPop

/-- One step remains: the second saved bit is restored and the first is
still stored in the finite mode. -/
theorem restore_pre (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (input higher : Nat) :
    run (Source284ModePrefixReturn.table continuation) ⟨4*input,higher,some (20+mode)⟩ 2 =
      ⟨2*higher+mode/2,2*input,some (28+mode)⟩ := by
  interval_cases mode <;>
    simp [run,step,Source284ModePrefixReturn.table,bit,Nat.testBit_zero,Nat.mul_mod] <;>
    congr 1 <;> try split_ifs
  all_goals repeat' constructor
  all_goals omega

theorem rest_pre (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (xs : List Bool) (higher suffix : Nat) :
    run (Source284ModePrefixReturn.table continuation)
      ⟨2*suffix,pushPairs (4*higher) xs,some (8+mode)⟩ (2*xs.length+4) =
      ⟨2*higher+mode/2,2*encodeFrame xs suffix,some (28+mode)⟩ := by
  have ht : 2*xs.length+4 = (2*xs.length)+2+2 := by omega
  rw [ht,Source284ModePrefixReturn.run_add,Source284ModePrefixReturn.run_add,
    Source284ModePrefixReturn.reverse_pairs _ _ hm,rawPairs_frame,
    Source284ModePrefixReturn.boundary _ _ hm,restore_pre _ _ hm]

theorem pop_pre (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 4)
    (xs : List Bool) (b : Bool) (higher suffix : Nat) :
    run (table continuation) ⟨2*pushPairs (4*higher) (xs++[b]),suffix,some mode⟩
      (2*(xs++[b]).length+6) =
      ⟨2*higher+mode/2,2*encodeFrame xs (4*suffix+bit b),some (48+mode)⟩ := by
  have ht : 2*(xs++[b]).length+6 = 2+(2+(2*xs.length+4)) := by simp; omega
  rw [ht,run_add,start _ _ hm,pushPairs_snoc,run_add,first_pair _ _ hm]
  have he : 4*(2*suffix)+2*(if b then 1 else 0) = 2*(4*suffix+bit b) := by
    cases b <;> simp [bit] <;> omega
  rw [he]
  change run (table continuation)
    (shiftConfig 20 ⟨2*(4*suffix+bit b),pushPairs (4*higher) xs,some (8+mode)⟩) _ = _
  rw [relocated_run,rest_pre _ _ hm]
  simp [shiftConfig]
  omega

/-- The whole pass has exactly one transition remaining; the target state
records the original two low certificate bits. -/
theorem full_pre (continuation : Nat → Bool → Row) (xs : List Bool) (b : Bool)
    (certificate suffix : Nat) :
    run (Source284InputSentinel.table (Source284ModePrefixScan.table (table continuation)))
      ⟨certificate,encodeFrame (xs++[b]) suffix,some 0⟩ (4*(xs++[b]).length+11) =
      ⟨2*(certificate/4)+(certificate%4)/2,
        2*encodeFrame xs (4*suffix+bit b),some (64+certificate%4)⟩ := by
  have hm : certificate%4 < 4 := Nat.mod_lt certificate (by decide)
  have ht : 4*(xs++[b]).length+11 = 4+((2*(xs++[b]).length+1)+
      (2*(xs++[b]).length+6)) := by omega
  rw [ht,run_add,Source284InputSentinel.prepare]
  change run (Source284InputSentinel.table (Source284ModePrefixScan.table (table continuation)))
    (shiftConfig 8 ⟨4*(certificate/4),encodeFrame (xs++[b]) suffix,some (certificate%4)⟩) _ = _
  rw [Source284InputSentinel.relocated_run,run_add,Source284ModePrefixScan.scan_frame _ _ hm]
  change shiftConfig 8 (run (Source284ModePrefixScan.table (table continuation))
    (shiftConfig 8 ⟨2*pushPairs (4*(certificate/4)) (xs++[b]),suffix,some (certificate%4)⟩) _) = _
  rw [Source284ModePrefixScan.relocated_run,pop_pre _ _ hm]
  simp [shiftConfig]
  omega

end Shared.Beeping.NPcoNP.Source284PayloadPopPrecise
