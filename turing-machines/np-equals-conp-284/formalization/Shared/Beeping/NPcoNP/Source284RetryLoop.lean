import Shared.Beeping.NPcoNP.Source284RetryGrowPre

/-! A finite table redirects the final retry turn back to the comparator.
Comparison equality and token-excess are routed to two supplied continuation
entries. The final transition of each retry is included in the proof. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284RetryLoop

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig shiftRow)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def sink (q : Nat) (b : Bool) : Row := ⟨b,false,some q⟩
def base : Nat → Bool → Row := Source284OneRetry.table sink

def returnRow (q : Nat) : Prop := q = 48 ∨ q = 50 ∨ q = 96

def sinkIndex (q : Nat) : Nat := if q = 48 then 98 else if q = 50 then 99 else 97

def targetIndex (q : Nat) : Nat := if q = 48 then 97 else if q = 50 then 98 else 0

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 48 ∨ q = 50 ∨ q = 96 then
    let r := base q b
    ⟨r.write,r.turn,some (targetIndex q)⟩
  else if q < 97 then base q b
  else shiftRow 97 (continuation (q-97) b)

theorem sink_closed : Closed 3 sink := by
  intro q hq b q' h
  simp [sink] at h
  omega

theorem base_closed : Closed 100 base := by
  have h := Source284OneRetry.closed 3 sink (by decide) sink_closed
  simpa [base] using h

/-- This finite row check is kernel reduced; it includes both exit states. -/
theorem finite_prefix : ∀ q : Fin 97, ∀ b : Bool,
    (table sink q.val b).next.getD 0 < 99 := by decide +kernel

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 2 ≤ states) (hv : Closed states continuation) : Closed (97+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases hs : q < 97
  · have he : table continuation q b = table sink q b := by simp [table,hs]
    have h := finite_prefix ⟨q,hs⟩ b
    rw [← he,hnext] at h
    simp at h
    omega
  · have hr : ¬(q = 48 ∨ q = 50 ∨ q = 96) := by omega
    have ht : (shiftRow 97 (continuation (q-97) b)).next = some q' := by
      simpa [table,hs,hr] using hnext
    have hq0 : q-97 < states := by omega
    cases he : (continuation (q-97) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hv (q-97) hq0 b r he
      simp [shiftRow,he] at ht
      subst q'
      omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (97+q) b = shiftRow 97 (continuation q b) := by
  have hs : ¬97+q < 97 := by omega
  have hr : ¬(97+q = 48 ∨ 97+q = 50 ∨ 97+q = 96) := by omega
  simp [table,hs,hr]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 97 c) = shiftConfig 97 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 97 c) fuel = shiftConfig 97 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem sink_row (q : Nat) (hq : 97 ≤ q) (hq' : q < 100) (b : Bool) :
    base q b = ⟨b,false,some q⟩ := by
  interval_cases q <;> cases b <;> rfl

theorem sink_step (c : Config) (q : Nat) (hq : 97 ≤ q) (hq' : q < 100)
    (h : c.state = some q) : (step base c).state = some q := by
  cases c with
  | mk left right state =>
    simp only at h
    subst state
    simp [step,sink_row q hq hq']

theorem sink_run (c : Config) (q : Nat) (hq : 97 ≤ q) (hq' : q < 100)
    (h : c.state = some q) (fuel : Nat) : (run base c fuel).state = some q := by
  induction fuel with
  | zero => exact h
  | succ fuel ih => exact sink_step _ q hq hq' ih

theorem final_step (c : Config) (q : Nat) (hq : returnRow q)
    (h : c.state = some q) : (step base c).state = some (sinkIndex q) := by
  cases c with
  | mk left right state =>
    simp only at h
    subst state
    rcases hq with rfl | rfl | rfl <;>
      simp [step,base,Source284OneRetry.table,Source284MatchLoop.table,Source284MatchLoop.base,
        Source284MatchStep.table,Source284UnaryMarkOne.table,Source284MatchDispatch.table,
        Source284RetryDispatch.table,Source284MatchGrow.table,Source284MatchReset.table,
        Source284UnaryClear.table,Source284PayloadReset.table,Source284ScratchFlipReturn.table,
        Source284ScratchShiftCycle.repeatTable,Source284ScratchShiftCycle.table,
        Source284ScratchShiftPipeline.entry,Source284ScratchShift.table,
        Source284ScratchShiftReturn.table,shiftRow,sink,sinkIndex]

theorem avoid_before_final (c : Config) (limit final : Nat)
    (hvalid : Valid 100 c) (hfinal : final < 97)
    (hfinish : (run base c limit).state = some final) :
    ∀ t < limit, ∀ q, (run base c t).state = some q → q < 97 ∧ ¬returnRow q := by
  intro t ht q hq
  have hbound : q < 100 := (valid_run 100 base c base_closed hvalid t) q hq
  have hsink : ∀ z, 97 ≤ z → z < 100 → (run base c t).state = some z → False := by
    intro z hz hz' hs
    have h := sink_run (run base c t) z hz hz' hs (limit-t)
    rw [← run_add] at h
    have ht' : t+(limit-t) = limit := by omega
    rw [ht',hfinish] at h
    have he : final = z := Option.some.inj h
    omega
  have hq97 : q < 97 := by
    by_contra hn
    have hn' : 97 ≤ q := by omega
    exact hsink q hn' hbound hq
  refine ⟨hq97,?_⟩
  intro hr
  have hn : (run base c (t+1)).state = some (sinkIndex q) := by
    simp only [run]
    exact final_step _ q hr hq
  have hi : 97 ≤ sinkIndex q ∧ sinkIndex q < 100 := by
    rcases hr with rfl | rfl | rfl <;> simp [sinkIndex]
  have h := sink_run (run base c (t+1)) (sinkIndex q) hi.1 hi.2 hn (limit-(t+1))
  rw [← run_add] at h
  have ht' : t+1+(limit-(t+1)) = limit := by omega
  rw [ht',hfinish] at h
  have he : final = sinkIndex q := Option.some.inj h
  omega

theorem run_agree (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat)
    (hrows : ∀ t < fuel, ∀ q, (run base c t).state = some q → q < 97 ∧ ¬returnRow q) :
    run (table continuation) c fuel = run base c fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have hp : ∀ t < fuel, ∀ q, (run base c t).state = some q → q < 97 ∧ ¬returnRow q := by
      intro t ht q hq
      exact hrows t (by omega) q hq
    simp only [run,ih hp]
    cases hc : run base c fuel with
    | mk left right state =>
      cases state with
      | none => rfl
      | some q =>
        have hq := hrows fuel (by omega) q (by simp [hc])
        have hn : ¬(q = 48 ∨ q = 50 ∨ q = 96) := hq.2
        simp [step,table,hn,hq.1]

theorem redirect_retry (continuation : Nat → Bool → Row) (stream left : Nat) :
    step (table continuation) ⟨2*stream,left,some 96⟩ = ⟨left,2*stream,some 0⟩ := by
  simp [step,table,base,Source284OneRetry.table,Source284MatchLoop.table,Source284MatchLoop.base,
    Source284MatchStep.table,Source284UnaryMarkOne.table,Source284MatchDispatch.table,
    Source284RetryDispatch.table,Source284MatchGrow.table,Source284MatchReset.table,
    Source284UnaryClear.table,Source284PayloadReset.table,Source284ScratchFlipReturn.table,
    Source284ScratchShiftCycle.repeatTable,Source284ScratchShiftCycle.table,
    Source284ScratchShiftPipeline.entry,Source284ScratchShift.table,
    Source284ScratchShiftReturn.table,shiftRow,targetIndex,bit,Nat.testBit_zero] <;>
    split_ifs <;> omega

/-- A single retry restarts the same fixed table after adding one token. -/
theorem retry (continuation : Nat → Bool → Row) (w rest : List Bool) (b : Bool)
    (certificate tail : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate w.length false) certificate,
        2*flipped ((w++b::rest)++[false]) tail,some 0⟩
      (Source284OneRetry.cost w.length ((w++b::rest).length)) =
    ⟨pairTape (List.replicate (w.length+1) false) certificate,
      2*flipped ((w++b::rest)++[false]) (tail/4),some 0⟩ := by
  let c : Config := ⟨pairTape (List.replicate w.length false) certificate,
    2*flipped ((w++b::rest)++[false]) tail,some 0⟩
  let limit := (4*w.length*w.length+20*w.length+16)+(4*w.length+12*(w++b::rest).length+39)
  have hv : Valid 100 c := by intro q hq; simp [c] at hq; subst q; omega
  have hp : run base c limit = ⟨2*flipped ((w++b::rest)++[false]) (tail/4),
      pairTape (List.replicate (w.length+1) false) certificate,some 96⟩ :=
    Source284RetryGrowPre.retry_pre sink w rest b certificate tail
  have hf : (run base c limit).state = some 96 := by rw [hp]
  have ha := run_agree continuation c limit (avoid_before_final c limit 96 hv (by omega) hf)
  have ht : Source284OneRetry.cost w.length ((w++b::rest).length) = limit+1 := by
    dsimp [Source284OneRetry.cost,limit]
    omega
  change run (table continuation) c _ = _
  rw [ht,run,ha,hp,redirect_retry]

theorem redirect_equal (continuation : Nat → Bool → Row) (left stream : Nat) :
    step (table continuation) ⟨left,2*stream,some 50⟩ = ⟨2*left,stream,some 98⟩ := by
  simp [step,table,base,Source284OneRetry.table,Source284MatchLoop.table,Source284MatchLoop.base,
    Source284MatchStep.table,Source284UnaryMarkOne.table,Source284MatchDispatch.table,
    Source284RetryDispatch.table,shiftRow,sink,targetIndex,bit,Nat.testBit_zero]

/-- Equal prepared lengths reach the caller's second continuation. The
additional dispatch step moves once over the scratch boundary, as stated. -/
theorem finish_equal (continuation : Nat → Bool → Row) (w : List Bool) (certificate tail : Nat) :
    run (table continuation) ⟨pairTape (List.replicate w.length false) certificate,
      2*flipped (w++[false]) tail,some 0⟩ (4*w.length*w.length+20*w.length+17) =
    ⟨2*pairTape (List.replicate w.length true) certificate,zeros w (flipped [false] tail),some 98⟩ := by
  let c : Config := ⟨pairTape (List.replicate w.length false) certificate,
    2*flipped (w++[false]) tail,some 0⟩
  let limit := 4*w.length*w.length+20*w.length+16
  have hv : Valid 100 c := by intro q hq; simp [c] at hq; subst q; omega
  have hp : run base c limit = ⟨pairTape (List.replicate w.length true) certificate,
      2*zeros w (flipped [false] tail),some 50⟩ := by
    exact Source284MatchLoopComplete.equal_length (Source284RetryDispatch.table sink) w certificate tail
  have hf : (run base c limit).state = some 50 := by rw [hp]
  have ha := run_agree continuation c limit (avoid_before_final c limit 50 hv (by omega) hf)
  have ht : 4*w.length*w.length+20*w.length+17 = limit+1 := by dsimp [limit]
  change run (table continuation) c _ = _
  rw [ht,run,ha,hp,redirect_equal]

end Shared.Beeping.NPcoNP.Source284RetryLoop
