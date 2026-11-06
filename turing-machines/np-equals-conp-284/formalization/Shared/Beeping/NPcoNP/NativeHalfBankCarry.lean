import Shared.Beeping.NPcoNP.NativeHalfState1Layout
import Shared.Beeping.NPcoNP.NativeHalfCarryDispatch

/-! Prepared exceptional HALF through the state-1 carry and state-27 scan.
The left carry is a supplied finite tape pattern. This is not blank-start
reachability or correctness of the complete HALF primitive. -/

namespace Shared.Beeping.NPcoNP.NativeHalfBankCarry

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
open Shared.Beeping.NPcoNP.NativeHalfReturnBank
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfCarryDispatch

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- A finite left carry suffices for the prepared exceptional path to reach
state 28, with exact whole-tape output and no beeps along the segment. -/
theorem exceptional_through_carry (back : Int → Bool) (gap : Int)
    (left values : List Nat) (k : Nat)
    (hm : downHolds back (gap-1) (List.replicate k true ++ [false])) :
    let suffix := leftSuffix left
    let base := before back gap suffix
    let b := gap + 1 + (suffix.length : Int)
    let t := preparedTape back gap left values
    ∃ n : Nat, 0 < n ∧ silentSegment machine
      (cfg 30 b (prior base b (false :: UnaryBank.encode values)))
      (cfg 28 (gap+3) (put (result t (gap-1) k) (gap+2) false)) n := by
  dsimp only
  obtain ⟨s, n, hs, hn, hrun⟩ := encoded_left_bank_return back gap left values
  have hlen : (bits s).length = (leftSuffix left).length := by
    have hl := congrArg List.length hs
    simpa [leftSuffix] using hl
  have hh : (gap + 1 + ((leftSuffix left).length : Int)) - (bits s).length - 2 = gap-1 := by
    rw [hlen]
    omega
  have hrun' : silentSegment machine
      (cfg 30 (gap+1+((leftSuffix left).length : Int))
        (prior (before back gap (leftSuffix left))
          (gap+1+((leftSuffix left).length : Int)) (false :: UnaryBank.encode values)))
      (cfg 1 (gap-1) (preparedTape back gap left values)) n := by
    change silentSegment machine
      (cfg 30 (gap+1+((leftSuffix left).length : Int))
        (prior (before back gap (leftSuffix left))
          (gap+1+((leftSuffix left).length : Int)) (false :: UnaryBank.encode values)))
      (cfg 1 ((gap+1+((leftSuffix left).length : Int)) - (bits s).length - 2)
        (preparedTape back gap left values)) n at hrun
    rw [hh] at hrun
    exact hrun
  have hpat := prepared_downHolds back gap (gap-1) left values _ (by omega) hm
  have hg := prepared_gap back gap left values
  have ha : preparedTape back gap left values ((gap-1)+1) = false := by
    have he : (gap-1)+1 = gap := by omega
    rw [he]; exact hg.1
  have hb : preparedTape back gap left values ((gap-1)+2) = false := by
    have he : (gap-1)+2 = gap+1 := by omega
    rw [he]; exact hg.2.1
  have hc : preparedTape back gap left values ((gap-1)+3) = true := by
    have he : (gap-1)+3 = gap+2 := by omega
    rw [he]; exact hg.2.2
  have hdispatch := dispatch (preparedTape back gap left values) (gap-1) k hpat
    ha hb hc
  refine ⟨n + (2*k+4), by omega, ?_⟩
  have hd := segAdd machine _ _ _ n (2*k+4) hrun' hdispatch
  have he₁ : gap-1+4 = gap+3 := by omega
  have he₂ : gap-1+3 = gap+2 := by omega
  rw [he₁, he₂] at hd
  exact hd

end Shared.Beeping.NPcoNP.NativeHalfBankCarry
