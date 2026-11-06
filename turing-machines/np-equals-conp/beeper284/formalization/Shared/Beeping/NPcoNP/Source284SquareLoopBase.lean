import Shared.Beeping.NPcoNP.Source284NestedGrowthSource
import Shared.Beeping.NPcoNP.Source284ReusableTokenLoop

/-! Reference control for a squared-workspace loop. State 1 of the adapter
is an exhaustion sink; successful entry runs a separate copy of the checked
growth round. Its completion reaches a second sink. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284SquareLoopBase

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)
open Shared.Beeping.NPcoNP.Source284ReusableTokenRound (roundCost)

def adapter (q : Nat) (b : Bool) : Row :=
  if q=0 then shiftRow 2 (Source284ReusableTokenLoop.base 0 b)
  else if q=1 then ⟨b,false,some 1⟩
  else shiftRow 2 (Source284ReusableTokenLoop.base (q-2) b)

def base : Nat → Bool → Row := Source284NestedBranchDispatch.table adapter

theorem adapter_closed : Closed 45 adapter := by
  intro q hq b q' hnext
  by_cases h0 : q=0
  · subst q
    have he : (shiftRow 2 (Source284ReusableTokenLoop.base 0 b)).next=some q' := by simpa [adapter] using hnext
    cases hh : (Source284ReusableTokenLoop.base 0 b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := Source284ReusableTokenLoop.base_closed 0 (by omega) b r hh
      simp [shiftRow,hh] at he; subst q'; omega
  · by_cases h1 : q=1
    · subst q; simp [adapter] at hnext; omega
    · have he : (shiftRow 2 (Source284ReusableTokenLoop.base (q-2) b)).next=some q' := by
        simpa [adapter,h0,h1] using hnext
      cases hh : (Source284ReusableTokenLoop.base (q-2) b).next with
      | none => simp [shiftRow,hh] at he
      | some r =>
        have hr := Source284ReusableTokenLoop.base_closed (q-2) (by omega) b r hh
        simp [shiftRow,hh] at he; subst q'; omega

theorem closed : Closed 88 base := by
  have hc := Source284NestedBranchSource.closed 45 adapter (by omega) adapter_closed
  simpa [base] using hc

theorem adapter_row (q : Nat) (b : Bool) :
    adapter (2+q) b = shiftRow 2 (Source284ReusableTokenLoop.base q b) := by
  simp [adapter,show 2+q ≠ 1 by omega]

theorem adapter_step (c : Config) :
    step adapter (shiftConfig 2 c) = shiftConfig 2 (step Source284ReusableTokenLoop.base c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,adapter_row,shiftRow]
      split <;> rfl

theorem adapter_run (c : Config) (fuel : Nat) :
    run adapter (shiftConfig 2 c) fuel = shiftConfig 2 (run Source284ReusableTokenLoop.base c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,adapter_step]

theorem adapter_jump (left right fuel : Nat) :
    run adapter ⟨left,right,some 0⟩ (fuel+1) =
      shiftConfig 2 (run Source284ReusableTokenLoop.base ⟨left,right,some 0⟩ (fuel+1)) := by
  rw [run_front,run_front]
  have hs : step adapter ⟨left,right,some 0⟩ =
      shiftConfig 2 (step Source284ReusableTokenLoop.base ⟨left,right,some 0⟩) := by
    simp [step,adapter,shiftRow,shiftConfig]
    split <;> rfl
  rw [hs,adapter_run]

theorem roundCost_ge_two (m n width : Nat) : 2 ≤ roundCost m n width := by
  simp [Source284ReusableTokenRound.roundCost]
  omega

/-- The successful round's last row is reached with the counter extended,
and the marker's two tape blocks restored. -/
theorem growth_pre (m k n : Nat) (rest w : List Bool) (certificate higher : Nat) :
    run base
      ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true ++ false::rest) certificate),
        2*flipped w (counter n higher),some 0⟩ (Source284NestedGrowthStep.cost m k n w.length-1) =
    ⟨2*flipped w (counter (n+m) (halves m higher)),
      pairTape (List.replicate m false) (pairTape (List.replicate k true ++ true::rest) certificate),some 86⟩ := by
  have hp : 0 < roundCost m n w.length-1 := by have := roundCost_ge_two m n w.length; omega
  have ht : Source284NestedGrowthStep.cost m k n w.length-1 =
      (4*m+4*k+14)+(roundCost m n w.length-1) := by
    simp [Source284NestedGrowthStep.cost]; omega
  rw [ht]
  unfold base
  rw [Source284NestedBranchDispatch.mark_then]
  have he : roundCost m n w.length-1 = (roundCost m n w.length-2)+1 := by omega
  rw [he,adapter_jump,← he]
  have hr := Source284ReusableTokenLoop.round_pre m n w
    (pairTape (List.replicate k true ++ true::rest) certificate) higher
  rw [hr]
  simp [shiftConfig]

/-- The exhaustion return reaches its distinct last row before its sink. -/
theorem exhausted_pre (m k certificate stream : Nat) :
    run base ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate),
      2*stream,some 0⟩ (4*m+4*k+13) =
    ⟨2*stream,pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate),some 41⟩ := by
  let c : Config := ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate),2*stream,some 0⟩
  let limit := 4*m+4*k+13
  have hv : Valid 43 c := by intro q hq; simp [c] at hq; subst q; omega
  have hr := Source284NestedBranchPre.exhausted_pre Source284NestedBranchDispatch.sink m k certificate stream
  change run Source284NestedBranchDispatch.base c limit = _ at hr
  have hf : (run Source284NestedBranchDispatch.base c limit).state = some 41 := by rw [hr]
  have he := Source284NestedBranchDispatch.run_agree adapter c hv limit
    (Source284NestedBranchDispatch.avoid_before c limit 41 (Or.inr rfl) hf)
  change run (Source284NestedBranchDispatch.table adapter) c limit = _
  rw [he,hr]

end Shared.Beeping.NPcoNP.Source284SquareLoopBase
