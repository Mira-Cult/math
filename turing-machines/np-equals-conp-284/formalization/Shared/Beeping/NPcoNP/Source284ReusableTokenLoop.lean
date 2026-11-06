import Shared.Beeping.NPcoNP.Source284ReusableTokenRound

/-! One fixed finite table repeats the token-transfer round forever. The
iteration count in the theorem is a proof index, not an implemented stopping
condition. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284ReusableTokenLoop

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (consumeTime halves)
open Shared.Beeping.NPcoNP.Source284ReusableTokenRound (roundCost)

def sink (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
def base : Nat → Bool → Row := Source284ReusableTokenRound.table sink

def table (q : Nat) (b : Bool) : Row :=
  if q = 41 then let r := base q b; ⟨r.write,r.turn,some 0⟩ else base q b

theorem base_closed : Closed 43 base := by
  have hs : Closed 1 sink := by intro q hq b q' hnext; simp [sink] at hnext; omega
  simpa [base] using Source284ReusableTokenRound.closed 1 sink (by omega) hs

theorem row41 (b : Bool) : base 41 b = ⟨b,true,some 42⟩ := by cases b <;> rfl

theorem row42 (b : Bool) : base 42 b = ⟨b,false,some 42⟩ := by cases b <;> rfl

theorem sink_step (c : Config) (h : c.state = some 42) : (step base c).state = some 42 := by
  cases c with
  | mk left right state =>
    simp only at h
    subst state
    simp [step,row42]

theorem sink_run (c : Config) (h : c.state = some 42) (fuel : Nat) :
    (run base c fuel).state = some 42 := by
  induction fuel with
  | zero => exact h
  | succ fuel ih => exact sink_step _ ih

theorem final_step (c : Config) (h : c.state = some 41) : (step base c).state = some 42 := by
  cases c with
  | mk left right state =>
    simp only at h
    subst state
    simp [step,row41]

theorem avoid_before_final (c : Config) (limit : Nat)
    (hfinal : (run base c limit).state = some 41) :
    ∀ t < limit, (run base c t).state ≠ some 41 := by
  intro t ht hq
  have hs : (run base c (t+1)).state = some 42 := by
    simp only [run]
    exact final_step _ hq
  have h := sink_run (run base c (t+1)) hs (limit-(t+1))
  rw [← Source284PayloadPop.run_add] at h
  have he : t+1+(limit-(t+1)) = limit := by omega
  rw [he,hfinal] at h
  contradiction

theorem run_agree (c : Config) (fuel : Nat)
    (hrows : ∀ t < fuel, (run base c t).state ≠ some 41) :
    run table c fuel = run base c fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have hp : ∀ t < fuel, (run base c t).state ≠ some 41 := by
      intro t ht
      exact hrows t (by omega)
    simp only [run,ih hp]
    cases hc : run base c fuel with
    | mk left right state =>
      cases state with
      | none => rfl
      | some q =>
        have hq : q ≠ 41 := by
          intro he
          subst q
          exact hrows fuel (by omega) (by simp [hc])
        simp [step,table,hq]

/-- The last reset row, before turning back to the original boundary. -/
theorem unary_clear_pre (continuation : Nat → Bool → Row) (xs : List Bool)
    (certificate stream : Nat) :
    run (Source284UnaryClear.table continuation) ⟨pairTape xs certificate,2*stream,some 0⟩
      (4*xs.length+5) =
      ⟨2*stream,pairTape (List.replicate xs.length false) certificate,some 6⟩ := by
  have ht : 4*xs.length+5 = 1+(2*xs.length+(3+(2*xs.length+1))) := by omega
  rw [ht,Source284PayloadPop.run_add]
  change run (Source284UnaryClear.table continuation)
    (step (Source284UnaryClear.table continuation) ⟨pairTape xs certificate,2*stream,some 0⟩) _ = _
  rw [Source284UnaryClear.startup]
  unfold pairTape
  rw [Source284PayloadPop.run_add,Source284UnaryClear.clear_pairs,
    Source284PayloadPop.run_add,Source284UnaryClear.sentinel,
    Source284PayloadPop.run_add,Source284UnaryClear.back_pairs]
  have hp : 4^xs.length = 2^(2*xs.length) := by rw [Nat.pow_mul]
  rw [hp,← Source284ScratchSentinel.unaryPairs_stack,← Source284UnaryPairScanner.zero_pairTape]
  simp [run,step,Source284UnaryClear.table,bit,Nat.testBit_zero,Nat.add_mod,pairTape]
  omega

/-- The round reaches its unique final redirect row after a positive finite
prefix, with the block reset and counter extended. -/
theorem round_pre (m n : Nat) (w : List Bool) (certificate higher : Nat) :
    run base ⟨pairTape (List.replicate m false) certificate,
      2*flipped w (counter n higher),some 0⟩ (roundCost m n w.length-1) =
      ⟨2*flipped w (counter (n+m) (halves m higher)),
        pairTape (List.replicate m false) certificate,some 41⟩ := by
  have ht : roundCost m n w.length-1 = consumeTime m 0 n w.length + (2+(4*m+5)) := by
    simp [Source284ReusableTokenRound.roundCost]; omega
  rw [ht]
  unfold base Source284ReusableTokenRound.table
  rw [run_add]
  have hc := Source284TokenCounterLoop.consume (Source284ReusableTokenRound.handoff sink)
    m 0 w n certificate higher
  simp only [List.replicate_zero,List.nil_append,Nat.zero_add] at hc
  rw [hc]
  change run (Source284TokenCounterLoop.table (Source284ReusableTokenRound.handoff sink))
    (shiftConfig 32 ⟨pairTape (List.replicate m true) certificate,
      2*flipped w (counter (n+m) (halves m higher)),some 1⟩) _ = _
  rw [Source284TokenCounterContinue.relocated_run]
  change shiftConfig 32 (run (Source284OrientationHandoff.table 0
    (Source284UnaryClear.table sink))
    ⟨pairTape (List.replicate m true) certificate,
      2*flipped w (counter (n+m) (halves m higher)),
      some (Source284OrientationHandoff.initialState false)⟩ _) = _
  rw [Source284OrientationHandoff.then_run]
  simp only [Source284OrientationHandoff.normalized,Bool.false_eq_true,ite_false,Prod.fst,Prod.snd]
  have he := unary_clear_pre sink (List.replicate m true) certificate
    (flipped w (counter (n+m) (halves m higher)))
  simp only [List.length_replicate] at he
  rw [he]
  simp [shiftConfig]

theorem redirected_final (left right : Nat) :
    step table ⟨2*right,left,some 41⟩ = ⟨left,2*right,some 0⟩ := by
  simp [step,table,row41,bit,Nat.testBit_zero] <;> split_ifs <;> omega

/-- The same finite table executes another full round and returns to state 0. -/
theorem iteration (m n : Nat) (w : List Bool) (certificate higher : Nat) :
    run table ⟨pairTape (List.replicate m false) certificate,
      2*flipped w (counter n higher),some 0⟩ (roundCost m n w.length) =
    ⟨pairTape (List.replicate m false) certificate,
      2*flipped w (counter (n+m) (halves m higher)),some 0⟩ := by
  let c : Config := ⟨pairTape (List.replicate m false) certificate,
      2*flipped w (counter n higher),some 0⟩
  let limit := roundCost m n w.length-1
  have hpre := round_pre m n w certificate higher
  have hf : (run base c limit).state = some 41 := by rw [hpre]
  have heq := run_agree c limit (avoid_before_final c limit hf)
  have ht : roundCost m n w.length = limit+1 := by
    dsimp [limit,Source284ReusableTokenRound.roundCost]; omega
  change run table c _ = _
  rw [ht,run,heq,hpre,redirected_final]

end Shared.Beeping.NPcoNP.Source284ReusableTokenLoop
