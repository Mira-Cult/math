import Shared.Beeping.NPcoNP.NativeHalfOddCleanupScan
import Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix

/-! The odd HALF cleanup from state 37 through the exact state-25 tape.
The supplied prepared tape is an interface condition, not reachability. -/
namespace Shared.Beeping.NPcoNP.NativeHalfOddCleanupComposed

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfOddCleanupScan
open Shared.Beeping.NPcoNP.NativeHalfOddCleanupSweep
open Shared.Beeping.NPcoNP.NativeHalfCleanupShape
open Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
open Shared.Beeping.NPcoNP.UnarySuffixShift

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The odd cleanup scans right to the appended reserve and back to the
prepared boundary. It produces exactly `postTape`, without a beep. -/
theorem odd_cleanup (base : Int → Bool) (b : Int) (values : List Nat) :
    silentSegment machine
      (cfg 37 (b+3) (after base (b+1) (false :: UnaryBank.encode values)))
      (cfg 25 b (postTape base b values))
      (2*(UnaryBank.encode values).length+7) := by
  obtain ⟨s,hs⟩ := cleanup_shape values
  have hm := down_after_zero_bank base (b+1) values
  have hm' : downHolds (after base (b+1) (false :: UnaryBank.encode values))
      (b+3+((false :: UnaryBank.encode values).length : Int)) (bits s ++ [false,false]) := by
    simpa [hs,Int.add_assoc] using hm
  have hf := scan37_after_zero_prefix base (b+1) values
  have hf' : silentSegment machine
      (cfg 37 (b+3) (after base (b+1) (false :: UnaryBank.encode values)))
      (cfg 38 (b+3+((false :: UnaryBank.encode values).length : Int))
        (after base (b+1) (false :: UnaryBank.encode values)))
      ((UnaryBank.encode values).length+3) := by
    dsimp only at hf
    convert hf using 1 <;> simp [Int.add_assoc] <;> omega
  have hb := odd_cleanup_sweep s _ _ hm'
  have hlen : (bits s).length=(UnaryBank.encode values).length+2 := by simp [hs]
  have hb' : silentSegment machine
      (cfg 38 (b+3+((false :: UnaryBank.encode values).length : Int))
        (after base (b+1) (false :: UnaryBank.encode values)))
      (cfg 25 b (postTape base b values)) ((UnaryBank.encode values).length+4) := by
    rw [hlen] at hb
    have hp : b+3+(((false :: UnaryBank.encode values).length : Nat) : Int)-
        (((UnaryBank.encode values).length+2 : Nat) : Int)-2=b := by
      simp only [List.length_cons,Nat.cast_succ]
      omega
    rw [hp] at hb
    simpa [postTape] using hb
  have h := segAdd machine _ _ _ ((UnaryBank.encode values).length+3)
    ((UnaryBank.encode values).length+4) hf' hb'
  convert h using 1 <;> omega

end Shared.Beeping.NPcoNP.NativeHalfOddCleanupComposed

#print axioms Shared.Beeping.NPcoNP.NativeHalfOddCleanupComposed.odd_cleanup
