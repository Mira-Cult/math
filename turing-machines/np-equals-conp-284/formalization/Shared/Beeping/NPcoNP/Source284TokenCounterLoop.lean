import Shared.Beeping.NPcoNP.Source284TokenCounterRound

/-! A finite-table loop for consuming prepared unary tokens. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284TokenCounterLoop

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig shiftRow)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def sink (q : Nat) (b : Bool) : Row := ⟨b,false,some q⟩
def base : Nat → Bool → Row := Source284TokenCounterRound.table sink

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 31 then
    let r := base q b
    ⟨r.write,r.turn,some 0⟩
  else Source284TokenCounterRound.table continuation q b

theorem sink_closed : Closed 2 sink := by
  intro q hq b q' h
  simp [sink] at h
  omega

theorem base_closed : Closed 34 base := by
  have h := Source284TokenCounterRound.closed 2 sink (by decide) sink_closed
  simpa [base] using h

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 2 ≤ states) (hv : Closed states continuation) : Closed (32+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases h : q = 31
  · simp [table,h] at hnext
    omega
  · apply Source284TokenCounterRound.closed states continuation hn hv q hq b q'
    simpa [table,h] using hnext

theorem sink_row (q : Nat) (hq : 32 ≤ q) (hq' : q < 34) (b : Bool) :
    base q b = ⟨b,false,some q⟩ := by
  interval_cases q <;> cases b <;> rfl

theorem sink_step (c : Config) (q : Nat) (hq : 32 ≤ q) (hq' : q < 34)
    (h : c.state = some q) : (step base c).state = some q := by
  cases c with
  | mk left right state =>
    simp only at h
    subst state
    simp [step,sink_row q hq hq']

theorem sink_run (c : Config) (q : Nat) (hq : 32 ≤ q) (hq' : q < 34)
    (h : c.state = some q) (fuel : Nat) : (run base c fuel).state = some q := by
  induction fuel with
  | zero => exact h
  | succ fuel ih => exact sink_step _ q hq hq' ih

theorem final_step (c : Config) (h : c.state = some 31) :
    (step base c).state = some 32 := by
  cases c with
  | mk left right state =>
    simp only at h
    subst state
    simp [step,base,Source284TokenCounterRound.table,Source284UnaryMarkOne.table,
      Source284TokenCounterRound.dispatch,Source284ScratchCounterExtend.table,
      Source284CounterExtend.table,Source284ScratchCounterSeed.afterSeed,
      Source284ScratchFlipReturn.table,shiftRow]

theorem avoid_before_final (c : Config) (limit final : Nat)
    (hvalid : Valid 34 c) (hfinal : final < 32)
    (hfinish : (run base c limit).state = some final) :
    ∀ t < limit, ∀ q, (run base c t).state = some q → q < 32 ∧ q ≠ 31 := by
  intro t ht q hq
  have hbound : q < 34 := (valid_run 34 base c base_closed hvalid t) q hq
  have hsink : ∀ z, 32 ≤ z → z < 34 → (run base c t).state = some z → False := by
    intro z hz hz' hs
    have h := sink_run (run base c t) z hz hz' hs (limit-t)
    rw [← run_add] at h
    have ht' : t+(limit-t) = limit := by omega
    rw [ht',hfinish] at h
    have he : final = z := Option.some.inj h
    omega
  have hq32 : q < 32 := by
    by_contra hn
    exact hsink q (by omega) hbound hq
  refine ⟨hq32,?_⟩
  intro hr
  subst q
  have hn : (run base c (t+1)).state = some 32 := by
    simp only [run]
    exact final_step _ hq
  have h := sink_run (run base c (t+1)) 32 (by omega) (by omega) hn (limit-(t+1))
  rw [← run_add] at h
  have ht' : t+1+(limit-(t+1)) = limit := by omega
  rw [ht',hfinish] at h
  have he : final = 32 := Option.some.inj h
  omega

theorem run_agree (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat)
    (hrows : ∀ t < fuel, ∀ q, (run base c t).state = some q → q < 32 ∧ q ≠ 31) :
    run (table continuation) c fuel = run base c fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have hp : ∀ t < fuel, ∀ q, (run base c t).state = some q → q < 32 ∧ q ≠ 31 := by
      intro t ht q hq
      exact hrows t (by omega) q hq
    simp only [run,ih hp]
    cases hc : run base c fuel with
    | mk left right state =>
      cases state with
      | none => rfl
      | some q =>
        have hq := hrows fuel (by omega) q (by simp [hc])
        have ht : Source284TokenCounterRound.table continuation q (right.testBit 0) =
            Source284TokenCounterRound.table sink q (right.testBit 0) := by
          have hsmall := hq.1
          interval_cases q <;>
            simp [Source284TokenCounterRound.table,Source284UnaryMarkOne.table,
              Source284TokenCounterRound.dispatch,Source284ScratchCounterExtend.table,
              Source284CounterExtend.table,Source284ScratchCounterSeed.afterSeed,
              Source284ScratchFlipReturn.table,shiftRow]
        simp only [Nat.testBit_zero] at ht
        simp [step,table,hq.2,base,ht]

theorem found_pre (k : Nat) (rest w : List Bool) (n certificate higher : Nat) :
    run base ⟨pairTape (List.replicate k true ++ false::rest) certificate,
      2*flipped w (counter n higher),some 0⟩ (4*k+4*w.length+2*n+23) =
    ⟨2*flipped w (counter (n+1) (higher/2)),
      pairTape (List.replicate k true ++ true::rest) certificate,some 31⟩ := by
  have ht : 4*k+4*w.length+2*n+23 = (4*k+6)+(2+(4*w.length+2*n+15)) := by omega
  rw [ht,run_add]
  change run (Source284UnaryMarkOne.table (Source284TokenCounterRound.dispatch sink))
    (run (Source284UnaryMarkOne.table (Source284TokenCounterRound.dispatch sink)) _ _) _ = _
  rw [Source284UnaryMarkOne.mark_first]
  change run (Source284UnaryMarkOne.table (Source284TokenCounterRound.dispatch sink))
    (shiftConfig 12 ⟨pairTape (List.replicate k true ++ true::rest) certificate,
      2*flipped w (counter n higher),some 0⟩) _ = _
  rw [Source284UnaryMarkOne.relocated_run,run_add,
    Source284TokenCounterRound.dispatch_two _ 0 (by decide)]
  change shiftConfig 12 (run (Source284TokenCounterRound.dispatch sink)
    (shiftConfig 4 ⟨pairTape (List.replicate k true ++ true::rest) certificate,
      2*flipped w (counter n higher),some 0⟩) _) = _
  rw [Source284TokenCounterRound.dispatch_relocated_run,
    Source284ScratchCounterExtend.extend_scratch_pre]
  rfl

theorem all_marked_pre (continuation : Nat → Bool → Row) (k certificate stream : Nat) :
    run (Source284UnaryMarkOne.table continuation)
      ⟨pairTape (List.replicate k true) certificate,2*stream,some 0⟩ (4*k+5) =
      ⟨2*stream,pairTape (List.replicate k true) certificate,some 11⟩ := by
  have ht : 4*k+5 = 1+(2*k+(3+(2*k+1))) := by omega
  rw [ht,run_add]
  change run (Source284UnaryMarkOne.table continuation)
    (step (Source284UnaryMarkOne.table continuation)
      ⟨pairTape (List.replicate k true) certificate,2*stream,some 0⟩) _ = _
  rw [Source284UnaryMarkOne.startup]
  unfold pairTape
  rw [run_add,Source284UnaryMarkOne.forward_prefix,run_add,Source284UnaryMarkOne.exhausted]
  change run (Source284UnaryMarkOne.table continuation) ⟨4*certificate+2,
    Source284ScratchScanner.push (2*stream+1) (List.replicate k true),some (6+1)⟩ _ = _
  rw [run_add,Source284UnaryMarkOne.back_prefix _ _ (by decide)]
  simp [run,step,Source284UnaryMarkOne.table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> try split_ifs
  all_goals omega

theorem found_step (continuation : Nat → Bool → Row) (k : Nat) (rest w : List Bool)
    (n certificate higher : Nat) :
    run (table continuation) ⟨pairTape (List.replicate k true ++ false::rest) certificate,
      2*flipped w (counter n higher),some 0⟩ (4*k+4*w.length+2*n+24) =
    ⟨pairTape (List.replicate k true ++ true::rest) certificate,
      2*flipped w (counter (n+1) (higher/2)),some 0⟩ := by
  let c : Config := ⟨pairTape (List.replicate k true ++ false::rest) certificate,
      2*flipped w (counter n higher),some 0⟩
  let t := 4*k+4*w.length+2*n+23
  have hp := found_pre k rest w n certificate higher
  have hv : Valid 34 c := by intro q hq; simp [c] at hq; omega
  have hf : (run base c t).state = some 31 := by rw [hp]
  have ha := run_agree continuation c t (avoid_before_final c t 31 hv (by omega) hf)
  have ht : 4*k+4*w.length+2*n+24 = t+1 := by dsimp [t]
  rw [ht,run_add,ha,hp]
  simp [run,step,table,base,Source284TokenCounterRound.table,Source284UnaryMarkOne.table,
    Source284TokenCounterRound.dispatch,Source284ScratchCounterExtend.table,
    Source284CounterExtend.table,Source284ScratchCounterSeed.afterSeed,
    Source284ScratchFlipReturn.table,shiftRow,bit,Nat.testBit_zero] <;> split_ifs <;> omega

theorem exhausted_step (continuation : Nat → Bool → Row) (k : Nat) (w : List Bool)
    (n certificate higher : Nat) :
    run (table continuation) ⟨pairTape (List.replicate k true) certificate,
      2*flipped w (counter n higher),some 0⟩ (4*k+8) =
    ⟨pairTape (List.replicate k true) certificate,
      2*flipped w (counter n higher),some 33⟩ := by
  let c : Config := ⟨pairTape (List.replicate k true) certificate,
      2*flipped w (counter n higher),some 0⟩
  let t := 4*k+5
  have hp : run base c t = ⟨2*flipped w (counter n higher),
      pairTape (List.replicate k true) certificate,some 11⟩ := by
    exact all_marked_pre _ _ _ _
  have hv : Valid 34 c := by intro q hq; simp [c] at hq; omega
  have hf : (run base c t).state = some 11 := by rw [hp]
  have ha := run_agree continuation c t (avoid_before_final c t 11 hv (by omega) hf)
  have ht : 4*k+8 = t+3 := by dsimp [t]
  rw [ht,run_add,ha,hp]
  have hturn (q q' left right : Nat)
      (hrow : ∀ b, table continuation q b = ⟨b,true,some q'⟩) :
      step (table continuation) ⟨left,right,some q⟩ = ⟨right,left,some q'⟩ := by
    simp [step,hrow,bit,Nat.testBit_zero]
    split_ifs <;> omega
  have h11 (b : Bool) : table continuation 11 b = ⟨b,true,some 13⟩ := by rfl
  have h13 (b : Bool) : table continuation 13 b = ⟨b,true,some 15⟩ := by rfl
  have h15 (b : Bool) : table continuation 15 b = ⟨b,true,some 33⟩ := by rfl
  simp only [run]
  rw [hturn _ _ _ _ h11,hturn _ _ _ _ h13,hturn _ _ _ _ h15]

/-- Positive finite execution time, including the final exhausted scan. -/
def consumeTime : Nat → Nat → Nat → Nat → Nat
  | 0, k, _, _ => 4*k+8
  | m+1, k, n, width => 4*k+4*width+2*n+24 + consumeTime m (k+1) (n+1) width

def halves : Nat → Nat → Nat
  | 0, value => value
  | m+1, value => halves m (value/2)

/-- Every prepared token is consumed in finite time. The same finite table
restarts after each successful extension and enters the exhaustion branch. -/
theorem consume (continuation : Nat → Bool → Row) (m k : Nat) (w : List Bool)
    (n certificate higher : Nat) :
    run (table continuation) ⟨pairTape (List.replicate k true ++ List.replicate m false) certificate,
      2*flipped w (counter n higher),some 0⟩ (consumeTime m k n w.length) =
    ⟨pairTape (List.replicate (k+m) true) certificate,
      2*flipped w (counter (n+m) (halves m higher)),some 33⟩ := by
  induction m generalizing k n higher with
  | zero => simpa [consumeTime,halves] using exhausted_step continuation k w n certificate higher
  | succ m ih =>
    simp only [consumeTime,List.replicate_succ]
    rw [run_add,found_step]
    have hmarks : List.replicate k true ++ true::List.replicate m false =
        List.replicate (k+1) true ++ List.replicate m false := by
      rw [List.replicate_add]
      simp [List.append_assoc]
    rw [hmarks]
    have hk : k+(m+1) = (k+1)+m := by omega
    have hn : n+(m+1) = (n+1)+m := by omega
    rw [hk,hn]
    exact ih (k+1) (n+1) (higher/2)

/-- Explicit quadratic cost in the number of prepared tokens. -/
theorem consumeTime_formula (m k n width : Nat) :
    consumeTime m k n width =
      3*m*m + m*(4*k+2*n+4*width+25)+4*k+8 := by
  induction m generalizing k n with
  | zero => simp [consumeTime]
  | succ m ih =>
    simp only [consumeTime,ih]
    ring

/-- Numeric source description includes every loop state and its continuation. -/
def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  encode (32+states) (table continuation) 1

/-- The autonomous run is also a run of the encoded numeric source program. -/
theorem source_consume (states : Nat) (continuation : Nat → Bool → Row)
    (m k : Nat) (w : List Bool) (n certificate higher : Nat)
    (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (2*flipped w (counter n higher))
        (pairTape (List.replicate k true ++ List.replicate m false) certificate))
      (consumeTime m k n w.length) =
    ⟨pairTape (List.replicate (k+m) true) certificate,
      2*flipped w (counter (n+m) (halves m higher)),active 33⟩ := by
  let c : Config := ⟨pairTape (List.replicate k true ++ List.replicate m false) certificate,
    2*flipped w (counter n higher),some 0⟩
  have hc : Valid (32+states) c := by intro q hq; simp [c] at hq; omega
  have h := run_toSource (32+states) (table continuation) 1 c
    (closed states continuation hn hv) hc (consumeTime m k n w.length)
  rw [consume] at h
  exact h

end Shared.Beeping.NPcoNP.Source284TokenCounterLoop
