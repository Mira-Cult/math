import Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
import Shared.Beeping.NPcoNP.NativeHalfCleanupScan
import Shared.Beeping.NPcoNP.NativeHalfCleanupShape

/-! Exact state-18 cleanup for a prepared zero-prefixed bank. This is a
local literal-table segment; entry reachability and the graph adapter are
separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeHalfEvenCleanup

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfCleanupScan
open Shared.Beeping.NPcoNP.NativeHalfCleanupShape
open Shared.Beeping.NPcoNP.NativeHalfCleanupSweep
open Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
open Shared.Beeping.NPcoNP.UnarySuffixShift

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- The even cleanup scans the bank and reserve, then sweeps back to state
23. The exact output tape and empty event word are recorded. -/
theorem cleanup18 (base : Int → Bool) (gap : Int) (values : List Nat) :
    silentSegment machine
      (cfg 18 (gap+1) (after base gap (false :: UnaryBank.encode values)))
      (cfg 23 (gap-1) (postTape base (gap-1) values))
      (2*(UnaryBank.encode values).length+8) := by
  obtain ⟨s,hs⟩ := cleanup_shape values
  have hm := down_after_zero_bank base gap values
  have hm' : downHolds (after base gap (false :: UnaryBank.encode values))
      (gap+2+((false :: UnaryBank.encode values).length : Int)) (bits s ++ [false,false]) := by
    simpa [hs] using hm
  have hf := scan_after_zero_prefix base gap values
  have hf' : silentSegment machine
      (cfg 18 (gap+1) (after base gap (false :: UnaryBank.encode values)))
      (cfg 20 (gap+2+((false :: UnaryBank.encode values).length : Int))
        (after base gap (false :: UnaryBank.encode values)))
      ((UnaryBank.encode values).length+4) := by
    dsimp only at hf
    have he : gap+1+((((false :: UnaryBank.encode values) ++ [true]).length : Nat) : Int) =
        gap+2+(((false :: UnaryBank.encode values).length : Nat) : Int) := by
      simp only [List.length_append,List.length_cons,List.length_nil,Nat.cast_add,Nat.cast_succ,Nat.cast_zero]
      omega
    have hn : ((false :: UnaryBank.encode values) ++ [true]).length+2 =
        (UnaryBank.encode values).length+4 := by simp
    rw [he,hn] at hf
    exact hf
  have hb := cleanup_sweep s _ _ hm'
  have hlen : (bits s).length=(UnaryBank.encode values).length+2 := by simp [hs]
  have hb' : silentSegment machine
      (cfg 20 (gap+2+((false :: UnaryBank.encode values).length : Int))
        (after base gap (false :: UnaryBank.encode values)))
      (cfg 23 (gap-1) (postTape base (gap-1) values))
      ((UnaryBank.encode values).length+4) := by
    rw [hlen] at hb
    have hp : gap+2+(((false :: UnaryBank.encode values).length : Nat) : Int)-
        (((UnaryBank.encode values).length+2 : Nat) : Int)-2=gap-1 := by
      simp only [List.length_cons,Nat.cast_succ]
      omega
    rw [hp] at hb
    have he : gap-1+1=gap := by omega
    have hpos : gap-1+3+(((false :: UnaryBank.encode values).length : Nat) : Int) =
        gap+2+(((false :: UnaryBank.encode values).length : Nat) : Int) := by omega
    simpa only [postTape,he,hpos] using hb
  have h := segAdd machine _ _ _ ((UnaryBank.encode values).length+4)
    ((UnaryBank.encode values).length+4) hf' hb'
  convert h using 1 <;> omega

end Shared.Beeping.NPcoNP.NativeHalfEvenCleanup

#print axioms Shared.Beeping.NPcoNP.NativeHalfEvenCleanup.cleanup18
