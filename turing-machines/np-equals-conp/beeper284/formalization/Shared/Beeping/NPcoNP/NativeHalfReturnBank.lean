import Shared.Beeping.NPcoNP.NativeHalfExceptionalReturn
import Shared.Beeping.NPcoNP.NativeHalfSweepShape

/-! A concrete finite unary left-bank instance of the prepared exceptional
return theorem. This supplies a delimiter, but not reachability from the
machine's blank tape. -/

namespace Shared.Beeping.NPcoNP.NativeHalfReturnBank

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
open Shared.Beeping.NPcoNP.NativeHalfExceptionalReturn

/-- An explicitly encoded finite left bank, followed by a one, provides
the first double-zero delimiter needed by the return scan. -/
theorem encoded_left_bank_return (back : Int → Bool) (gap : Int)
    (left values : List Nat) :
    let suffix := UnaryBank.encode left ++ [true]
    let base := before back gap suffix
    let b := gap + 1 + (suffix.length : Int)
    ∃ (s : Shape) (n : Nat), bits s = suffix.reverse ∧ 0 < n ∧
      silentSegment machine
        (cfg 30 b (prior base b (false :: UnaryBank.encode values)))
        (cfg 1 (b - (bits s).length - 2) (postTape base b values)) n := by
  dsimp only
  obtain ⟨s, hs⟩ := shape_reverse_bank left
  let suffix := UnaryBank.encode left ++ [true]
  let base := before back gap suffix
  let b := gap + 1 + (suffix.length : Int)
  have hbits : bits (Shape.one s) = suffix.reverse := by
    simp [bits, hs, suffix, List.reverse_append]
  have hpat : downHolds base b (bits (Shape.one s) ++ [false,false]) := by
    rw [hbits]
    exact down_before_reverse back gap suffix
  have hb : base b = true := by
    simpa [bits, downHolds] using hpat.1
  obtain ⟨n, hn, he⟩ := exceptional_return base b values (Shape.one s) hb hpat
  exact ⟨Shape.one s, n, hbits, hn, he⟩

end Shared.Beeping.NPcoNP.NativeHalfReturnBank
