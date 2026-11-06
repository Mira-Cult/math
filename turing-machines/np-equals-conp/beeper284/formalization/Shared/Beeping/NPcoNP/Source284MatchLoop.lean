import Shared.Beeping.NPcoNP.Source284MatchStep

/-! An autonomous paired comparison on a prepared tape. Matching pairs
restart; either mismatch or simultaneous exhaustion enters a distinct finite
continuation. All final-turn changes preserve the row's write and movement. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284MatchLoop

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig shiftRow)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def sink (q : Nat) (b : Bool) : Row := ⟨b,false,some q⟩
def base : Nat → Bool → Row := Source284MatchStep.table sink

def returnRow (q : Nat) : Prop := q = 28 ∨ q = 29 ∨ q = 45 ∨ q = 46

def sinkIndex (q : Nat) : Nat :=
  if q = 28 then 48 else if q = 29 then 49 else if q = 45 then 50 else 51

def targetIndex (q : Nat) : Nat :=
  if q = 28 then 0 else if q = 29 then 48 else if q = 45 then 49 else 50

/-- Four actual final-turn rows: match restarts, the remaining cases select
three distinct continuation entries. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 28 ∨ q = 29 ∨ q = 45 ∨ q = 46 then
    let r := base q b
    ⟨r.write,r.turn,some (targetIndex q)⟩
  else Source284MatchStep.table continuation q b

theorem sink_closed : Closed 4 sink := by
  intro q hq b q' h
  simp [sink] at h
  omega

theorem base_closed : Closed 52 base := by
  have h := Source284MatchStep.closed 4 sink (by decide) sink_closed
  simpa [base] using h

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 4 ≤ states) (hv : Closed states continuation) : Closed (48+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases hr : q = 28 ∨ q = 29 ∨ q = 45 ∨ q = 46
  · rcases hr with rfl | rfl | rfl | rfl <;> simp [table,targetIndex] at hnext <;> omega
  · have h := Source284MatchStep.closed states continuation hn hv q hq b q'
    apply h
    simpa [table,hr] using hnext

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (48+q) b = shiftRow 48 (continuation q b) := by
  have he : 48+q = 12+(36+q) := by omega
  rw [he]
  have hn : ¬(12+(36+q) = 28 ∨ 12+(36+q) = 29 ∨ 12+(36+q) = 45 ∨ 12+(36+q) = 46) := by omega
  simp only [table,hn,if_false,Source284MatchStep.table,
    Source284UnaryMarkOne.relocated_row,Source284MatchDispatch.relocated_row]
  cases h : (continuation q b).next <;> simp [shiftRow,h,← Nat.add_assoc]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 48 c) = shiftConfig 48 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 48 c) fuel = shiftConfig 48 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem sink_row (q : Nat) (hq : 48 ≤ q) (hq' : q < 52) (b : Bool) :
    base q b = ⟨b,false,some q⟩ := by
  interval_cases q <;> cases b <;> rfl

theorem sink_step (c : Config) (q : Nat) (hq : 48 ≤ q) (hq' : q < 52)
    (h : c.state = some q) : (step base c).state = some q := by
  cases c with
  | mk left right state =>
    simp only at h
    subst state
    simp [step,sink_row q hq hq']

theorem sink_run (c : Config) (q : Nat) (hq : 48 ≤ q) (hq' : q < 52)
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
    rcases hq with rfl | rfl | rfl | rfl <;>
      simp [step,base,Source284MatchStep.table,Source284UnaryMarkOne.table,
        Source284MatchDispatch.table,shiftRow,sinkIndex]

theorem avoid_before_final (c : Config) (limit final : Nat)
    (hvalid : Valid 52 c) (hfinal : final < 48)
    (hfinish : (run base c limit).state = some final) :
    ∀ t < limit, ∀ q, (run base c t).state = some q → q < 48 ∧ ¬returnRow q := by
  intro t ht q hq
  have hbound : q < 52 := (valid_run 52 base c base_closed hvalid t) q hq
  have hsink : ∀ z, 48 ≤ z → z < 52 → (run base c t).state = some z → False := by
    intro z hz hz' hs
    have h := sink_run (run base c t) z hz hz' hs (limit-t)
    rw [← run_add] at h
    have ht' : t+(limit-t) = limit := by omega
    rw [ht',hfinish] at h
    have he : final = z := Option.some.inj h
    omega
  have hq48 : q < 48 := by
    by_contra hn
    have hn' : 48 ≤ q := by omega
    exact hsink q hn' hbound hq
  refine ⟨hq48,?_⟩
  intro hr
  have hn : (run base c (t+1)).state = some (sinkIndex q) := by
    simp only [run]
    exact final_step _ q hr hq
  have hi : 48 ≤ sinkIndex q ∧ sinkIndex q < 52 := by
    rcases hr with rfl | rfl | rfl | rfl <;> simp [sinkIndex]
  have h := sink_run (run base c (t+1)) (sinkIndex q) hi.1 hi.2 hn (limit-(t+1))
  rw [← run_add] at h
  have ht' : t+1+(limit-(t+1)) = limit := by omega
  rw [ht',hfinish] at h
  have he : final = sinkIndex q := Option.some.inj h
  omega

theorem run_agree (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat)
    (hrows : ∀ t < fuel, ∀ q, (run base c t).state = some q → q < 48 ∧ ¬returnRow q) :
    run (table continuation) c fuel = run base c fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have hp : ∀ t < fuel, ∀ q, (run base c t).state = some q → q < 48 ∧ ¬returnRow q := by
      intro t ht q hq
      exact hrows t (by omega) q hq
    simp only [run,ih hp]
    cases hc : run base c fuel with
    | mk left right state =>
      cases state with
      | none => rfl
      | some q =>
        have hq := hrows fuel (by omega) q (by simp [hc])
        have ht : Source284MatchStep.table continuation q (right.testBit 0) =
            Source284MatchStep.table sink q (right.testBit 0) := by
          have hsmall := hq.1
          interval_cases q <;>
            simp [Source284MatchStep.table,Source284UnaryMarkOne.table,Source284MatchDispatch.table,
              Source284PayloadMarkLoop.base,Source284PayloadMarkOne.table,shiftRow]
        simp only [Nat.testBit_zero] at ht
        have hn : ¬(q = 28 ∨ q = 29 ∨ q = 45 ∨ q = 46) := hq.2
        simp [step,table,hn,base,ht]

/-- The selected dispatch copy is at its success return one step before the
paired step completes. -/
theorem dispatch_mark_pre (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 2)
    (xs ys : List Bool) (b c : Bool) (left tail : Nat) :
    run (Source284MatchDispatch.table continuation)
      ⟨left,2*zeros xs (flipped (b::c::ys) tail),some mode⟩ (4*xs.length+9) =
      shiftConfig (Source284MatchDispatch.offset mode)
        ⟨2*zeros (xs++[b]) (flipped (c::ys) tail),left,some 14⟩ := by
  have hp := Source284PayloadMarkLoop.mark_pre xs ys b c left tail
  have hf : (run Source284PayloadMarkLoop.base
      ⟨left,2*zeros xs (flipped (b::c::ys) tail),some 0⟩ (4*xs.length+9)).state = some 14 := by
    rw [hp]
  rw [Source284MatchDispatch.to_pre continuation mode hm left (zeros xs (flipped (b::c::ys) tail))
    (4*xs.length+9) 14 (by omega) (Or.inl rfl) hf,hp]

theorem dispatch_exhausted_pre (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 2)
    (xs : List Bool) (left tail : Nat) :
    run (Source284MatchDispatch.table continuation)
      ⟨left,2*zeros xs (flipped [false] tail),some mode⟩ (4*xs.length+9) =
      shiftConfig (Source284MatchDispatch.offset mode)
        ⟨2*zeros xs (flipped [false] tail),left,some 15⟩ := by
  have hp := Source284PayloadMarkLoop.exhausted_pre xs left tail
  have hf : (run Source284PayloadMarkLoop.base
      ⟨left,2*zeros xs (flipped [false] tail),some 0⟩ (4*xs.length+9)).state = some 15 := by
    rw [hp]
  rw [Source284MatchDispatch.to_pre continuation mode hm left (zeros xs (flipped [false] tail))
    (4*xs.length+9) 15 (by omega) (Or.inr rfl) hf,hp]

theorem both_pre (k : Nat) (tokens : List Bool) (xs ys : List Bool) (b c : Bool) (certificate tail : Nat) :
    run base ⟨pairTape (List.replicate k true ++ false::tokens) certificate,
      2*zeros xs (flipped (b::c::ys) tail),some 0⟩ (4*k+6+(4*xs.length+9)) =
    ⟨2*zeros (xs++[b]) (flipped (c::ys) tail),
      pairTape (List.replicate k true ++ true::tokens) certificate,some 28⟩ := by
  unfold base Source284MatchStep.table
  rw [run_add,Source284UnaryMarkOne.mark_first]
  change run (Source284UnaryMarkOne.table (Source284MatchDispatch.table sink))
    (shiftConfig 12 ⟨pairTape (List.replicate k true ++ true::tokens) certificate,
      2*zeros xs (flipped (b::c::ys) tail),some 0⟩) _ = _
  rw [Source284UnaryMarkOne.relocated_run,dispatch_mark_pre _ 0 (by decide)]
  rfl

theorem token_pre (k : Nat) (tokens : List Bool) (xs : List Bool) (certificate tail : Nat) :
    run base ⟨pairTape (List.replicate k true ++ false::tokens) certificate,
      2*zeros xs (flipped [false] tail),some 0⟩ (4*k+6+(4*xs.length+9)) =
    ⟨2*zeros xs (flipped [false] tail),
      pairTape (List.replicate k true ++ true::tokens) certificate,some 29⟩ := by
  unfold base Source284MatchStep.table
  rw [run_add,Source284UnaryMarkOne.mark_first]
  change run (Source284UnaryMarkOne.table (Source284MatchDispatch.table sink))
    (shiftConfig 12 ⟨pairTape (List.replicate k true ++ true::tokens) certificate,
      2*zeros xs (flipped [false] tail),some 0⟩) _ = _
  rw [Source284UnaryMarkOne.relocated_run,dispatch_exhausted_pre _ 0 (by decide)]
  rfl

theorem payload_pre (k : Nat) (xs ys : List Bool) (b c : Bool) (certificate tail : Nat) :
    run base ⟨pairTape (List.replicate k true) certificate,
      2*zeros xs (flipped (b::c::ys) tail),some 0⟩ (4*k+6+(4*xs.length+9)) =
    ⟨2*zeros (xs++[b]) (flipped (c::ys) tail),
      pairTape (List.replicate k true) certificate,some 45⟩ := by
  unfold base Source284MatchStep.table
  rw [run_add,Source284UnaryMarkOne.all_marked]
  change run (Source284UnaryMarkOne.table (Source284MatchDispatch.table sink))
    (shiftConfig 12 ⟨pairTape (List.replicate k true) certificate,
      2*zeros xs (flipped (b::c::ys) tail),some 1⟩) _ = _
  rw [Source284UnaryMarkOne.relocated_run,dispatch_mark_pre _ 1 (by decide)]
  rfl

theorem exhausted_pre (k : Nat) (xs : List Bool) (certificate tail : Nat) :
    run base ⟨pairTape (List.replicate k true) certificate,
      2*zeros xs (flipped [false] tail),some 0⟩ (4*k+6+(4*xs.length+9)) =
    ⟨2*zeros xs (flipped [false] tail),pairTape (List.replicate k true) certificate,some 46⟩ := by
  unfold base Source284MatchStep.table
  rw [run_add,Source284UnaryMarkOne.all_marked]
  change run (Source284UnaryMarkOne.table (Source284MatchDispatch.table sink))
    (shiftConfig 12 ⟨pairTape (List.replicate k true) certificate,
      2*zeros xs (flipped [false] tail),some 1⟩) _ = _
  rw [Source284UnaryMarkOne.relocated_run,dispatch_exhausted_pre _ 1 (by decide)]
  rfl

theorem redirect (continuation : Nat → Bool → Row) (q : Nat) (hr : returnRow q)
    (stream left : Nat) :
    step (table continuation) ⟨2*stream,left,some q⟩ =
      ⟨left,2*stream,some (targetIndex q)⟩ := by
  rcases hr with rfl | rfl | rfl | rfl <;>
    simp [step,table,base,Source284MatchStep.table,Source284UnaryMarkOne.table,
      Source284MatchDispatch.table,shiftRow,targetIndex,bit,Nat.testBit_zero] <;>
    split_ifs <;> omega

/-- The modified table agrees with the reference until its final row, then
executes the redirected final transition. -/
theorem redirect_pre (continuation : Nat → Bool → Row) (conf : Config) (limit q : Nat)
    (stream left : Nat) (hv : Valid 52 conf) (hr : returnRow q)
    (hp : run base conf limit = ⟨2*stream,left,some q⟩) :
    run (table continuation) conf (limit+1) = ⟨left,2*stream,some (targetIndex q)⟩ := by
  have hq : q < 48 := by rcases hr with rfl | rfl | rfl | rfl <;> omega
  have hf : (run base conf limit).state = some q := by rw [hp]
  have ha := run_agree continuation conf limit (avoid_before_final conf limit q hv hq hf)
  rw [run,ha,hp,redirect continuation q hr]

theorem both_step (continuation : Nat → Bool → Row) (k : Nat) (tokens : List Bool)
    (xs ys : List Bool) (b c : Bool) (certificate tail : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate k true ++ false::tokens) certificate,
        2*zeros xs (flipped (b::c::ys) tail),some 0⟩ (4*k+6+(4*xs.length+10)) =
    ⟨pairTape (List.replicate k true ++ true::tokens) certificate,
      2*zeros (xs++[b]) (flipped (c::ys) tail),some 0⟩ := by
  let conf : Config := ⟨pairTape (List.replicate k true ++ false::tokens) certificate,
    2*zeros xs (flipped (b::c::ys) tail),some 0⟩
  have hv : Valid 52 conf := by intro q hq; simp [conf] at hq; subst q; omega
  have hp := both_pre k tokens xs ys b c certificate tail
  have h := redirect_pre continuation conf (4*k+6+(4*xs.length+9)) 28
    (zeros (xs++[b]) (flipped (c::ys) tail))
    (pairTape (List.replicate k true ++ true::tokens) certificate) hv (Or.inl rfl) hp
  have ht : 4*k+6+(4*xs.length+10) = (4*k+6+(4*xs.length+9))+1 := by omega
  simpa [conf,ht,targetIndex] using h

theorem token_step (continuation : Nat → Bool → Row) (k : Nat) (tokens : List Bool)
    (xs : List Bool) (certificate tail : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate k true ++ false::tokens) certificate,
        2*zeros xs (flipped [false] tail),some 0⟩ (4*k+6+(4*xs.length+10)) =
    ⟨pairTape (List.replicate k true ++ true::tokens) certificate,
      2*zeros xs (flipped [false] tail),some 48⟩ := by
  let conf : Config := ⟨pairTape (List.replicate k true ++ false::tokens) certificate,
    2*zeros xs (flipped [false] tail),some 0⟩
  have hv : Valid 52 conf := by intro q hq; simp [conf] at hq; subst q; omega
  have hp := token_pre k tokens xs certificate tail
  have h := redirect_pre continuation conf (4*k+6+(4*xs.length+9)) 29
    (zeros xs (flipped [false] tail))
    (pairTape (List.replicate k true ++ true::tokens) certificate) hv (Or.inr (Or.inl rfl)) hp
  have ht : 4*k+6+(4*xs.length+10) = (4*k+6+(4*xs.length+9))+1 := by omega
  simpa [conf,ht,targetIndex] using h

theorem payload_step (continuation : Nat → Bool → Row) (k : Nat)
    (xs ys : List Bool) (b c : Bool) (certificate tail : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate k true) certificate,
        2*zeros xs (flipped (b::c::ys) tail),some 0⟩ (4*k+6+(4*xs.length+10)) =
    ⟨pairTape (List.replicate k true) certificate,
      2*zeros (xs++[b]) (flipped (c::ys) tail),some 49⟩ := by
  let conf : Config := ⟨pairTape (List.replicate k true) certificate,
    2*zeros xs (flipped (b::c::ys) tail),some 0⟩
  have hv : Valid 52 conf := by intro q hq; simp [conf] at hq; subst q; omega
  have hp := payload_pre k xs ys b c certificate tail
  have h := redirect_pre continuation conf (4*k+6+(4*xs.length+9)) 45
    (zeros (xs++[b]) (flipped (c::ys) tail)) (pairTape (List.replicate k true) certificate)
    hv (Or.inr (Or.inr (Or.inl rfl))) hp
  have ht : 4*k+6+(4*xs.length+10) = (4*k+6+(4*xs.length+9))+1 := by omega
  simpa [conf,ht,targetIndex] using h

theorem exhausted_step (continuation : Nat → Bool → Row) (k : Nat)
    (xs : List Bool) (certificate tail : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate k true) certificate,
        2*zeros xs (flipped [false] tail),some 0⟩ (4*k+6+(4*xs.length+10)) =
    ⟨pairTape (List.replicate k true) certificate,2*zeros xs (flipped [false] tail),some 50⟩ := by
  let conf : Config := ⟨pairTape (List.replicate k true) certificate,
    2*zeros xs (flipped [false] tail),some 0⟩
  have hv : Valid 52 conf := by intro q hq; simp [conf] at hq; subst q; omega
  have hp := exhausted_pre k xs certificate tail
  have h := redirect_pre continuation conf (4*k+6+(4*xs.length+9)) 46
    (zeros xs (flipped [false] tail)) (pairTape (List.replicate k true) certificate)
    hv (Or.inr (Or.inr (Or.inr rfl))) hp
  have ht : 4*k+6+(4*xs.length+10) = (4*k+6+(4*xs.length+9))+1 := by omega
  simpa [conf,ht,targetIndex] using h

end Shared.Beeping.NPcoNP.Source284MatchLoop
