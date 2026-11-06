import Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
import Shared.Beeping.NPcoNP.NativeHalfReturn23

/-! Prepared exceptional HALF execution through the inherited return scan.
The left delimiter is an explicit premise; nothing here asserts that a
blank-start run reaches this configuration or that state 1 is the selector. -/

namespace Shared.Beeping.NPcoNP.NativeHalfExceptionalReturn

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfCleanupComposed
open Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
open Shared.Beeping.NPcoNP.NativeHalfReturn23
open Shared.Beeping.NPcoNP.NativeHalfCycleTape

/-- With a supplied finite delimiter in the protected left prefix, the
exceptional HALF path and the return scan complete with no events. -/
theorem exceptional_return (base : Int → Bool) (b : Int) (values : List Nat)
    (s : Shape) (hb : base b = true)
    (hm : downHolds base b (bits s ++ [false,false])) :
    ∃ n : Nat, 0 < n ∧ silentSegment machine
      (cfg 30 b (prior base b (false :: UnaryBank.encode values)))
      (cfg 1 (b - (bits s).length - 2) (postTape base b values)) n := by
  obtain ⟨k, hk, hclean⟩ := exceptional_through_cleanup base b values hb
  have hclean' : silentSegment machine
      (cfg 30 b (prior base b (false :: UnaryBank.encode values)))
      (cfg 23 b (postTape base b values)) k := by
    simpa [postTape] using hclean
  have hpattern := downHolds_postTape base b b values (bits s ++ [false,false]) (by omega) hm
  have hreturn := return_scan s b (postTape base b values) hpattern
  exact ⟨k + ((bits s).length + 2), by omega,
    segAdd machine _ _ _ _ _ hclean' hreturn⟩

end Shared.Beeping.NPcoNP.NativeHalfExceptionalReturn
