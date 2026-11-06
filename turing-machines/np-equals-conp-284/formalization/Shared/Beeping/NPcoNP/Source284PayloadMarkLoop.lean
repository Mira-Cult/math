import Shared.Beeping.NPcoNP.Source284PayloadMarkOne

/-! An autonomous finite loop around the payload marker. The success return
restarts the scanner; the exhaustion return enters a finite continuation.
The source proof uses an absorbing reference table only for reasoning. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
namespace Shared.Beeping.NPcoNP.Source284PayloadMarkLoop

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig shiftRow)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros push)

def sink (q : Nat) (b : Bool) : Row := ⟨b,false,some q⟩
def base : Nat → Bool → Row := Source284PayloadMarkOne.table sink

/-- Redirect the two final return transitions, preserving their writes and
moves. State 14 restarts, while state 15 enters continuation state zero. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 14 then let r := base q b; ⟨r.write,r.turn,some 0⟩
  else if q = 15 then let r := base q b; ⟨r.write,r.turn,some 17⟩
  else Source284PayloadMarkOne.table continuation q b

theorem sink_closed : Closed 2 sink := by
  intro q hq b q' h
  simp [sink] at h
  omega

theorem base_closed : Closed 19 base := by
  have h := Source284PayloadMarkOne.closed 2 sink (by decide) sink_closed
  simpa [base] using h

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 2 ≤ states) (hv : Closed states continuation) : Closed (17+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases h14 : q = 14
  · subst q; simp [table] at hnext; omega
  · by_cases h15 : q = 15
    · subst q; simp [table,h14] at hnext; omega
    · have h := Source284PayloadMarkOne.closed states continuation hn hv q hq b q'
      apply h
      simpa [table,h14,h15] using hnext

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (17+q) b = shiftRow 17 (continuation q b) := by
  have h14 : 17+q ≠ 14 := by omega
  have h15 : 17+q ≠ 15 := by omega
  simp [table,h14,h15,Source284PayloadMarkOne.relocated_row]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 17 c) = shiftConfig 17 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 17 c) fuel = shiftConfig 17 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

/-- The reference states 17 and 18 are absorbing. -/
theorem sink_row (q : Nat) (hq : q = 17 ∨ q = 18) (b : Bool) :
    base q b = ⟨b,false,some q⟩ := by
  rcases hq with rfl | rfl <;> cases b <;> rfl

theorem sink_step (c : Config) (q : Nat) (hq : q = 17 ∨ q = 18)
    (h : c.state = some q) : (step base c).state = some q := by
  cases c with
  | mk left right state =>
    simp only at h
    subst state
    simp [step,sink_row q hq]

theorem sink_run (c : Config) (q : Nat) (hq : q = 17 ∨ q = 18)
    (h : c.state = some q) (fuel : Nat) : (run base c fuel).state = some q := by
  induction fuel with
  | zero => exact h
  | succ fuel ih => exact sink_step _ q hq ih

theorem final_rows (b : Bool) : (base 14 b).next = some 17 ∧ (base 15 b).next = some 18 := by
  cases b <;> constructor <;> rfl

theorem final_step (c : Config) (q : Nat) (hq : q = 14 ∨ q = 15)
    (h : c.state = some q) :
    (step base c).state = some (q+3) := by
  cases c with
  | mk left right state =>
    simp only at h
    subst state
    rcases hq with rfl | rfl <;> simp [step,base,Source284PayloadMarkOne.table]

/-- The reference run cannot enter either final row or either absorbing
state before reaching a specified final row. -/
theorem avoid_before_final (c : Config) (limit final : Nat)
    (hvalid : Valid 19 c) (hfinal : final = 14 ∨ final = 15)
    (hfinish : (run base c limit).state = some final) :
    ∀ t < limit, ∀ q, (run base c t).state = some q → q < 17 ∧ q ≠ 14 ∧ q ≠ 15 := by
  intro t ht q hq
  have hbound : q < 19 := (valid_run 19 base c base_closed hvalid t) q hq
  have hnot : q ≠ 14 ∧ q ≠ 15 ∧ q ≠ 17 ∧ q ≠ 18 := by
    have ha : ∀ z, (z = 17 ∨ z = 18) → (run base c t).state = some z → False := by
      intro z hz hs
      have h := sink_run (run base c t) z hz hs (limit-t)
      rw [← run_add] at h
      have ht' : t+(limit-t) = limit := by omega
      rw [ht',hfinish] at h
      rcases hfinal with rfl | rfl <;> rcases hz with rfl | rfl <;> contradiction
    have hb : ∀ z, (z = 14 ∨ z = 15) → (run base c t).state = some z → False := by
      intro z hz hs
      have hn : (run base c (t+1)).state = some (z+3) := by
        simp only [run]
        exact final_step _ z hz hs
      have hz' : z+3 = 17 ∨ z+3 = 18 := by rcases hz with rfl | rfl <;> simp
      have h := sink_run (run base c (t+1)) (z+3) hz' hn (limit-(t+1))
      rw [← run_add] at h
      have ht' : t+1+(limit-(t+1)) = limit := by omega
      rw [ht',hfinish] at h
      rcases hfinal with rfl | rfl <;> rcases hz with rfl | rfl <;> contradiction
    refine ⟨?_,?_,?_,?_⟩
    · intro h; exact hb 14 (Or.inl rfl) (h ▸ hq)
    · intro h; exact hb 15 (Or.inr rfl) (h ▸ hq)
    · intro h; exact ha 17 (Or.inl rfl) (h ▸ hq)
    · intro h; exact ha 18 (Or.inr rfl) (h ▸ hq)
  omega

theorem run_agree (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat)
    (hrows : ∀ t < fuel, ∀ q, (run base c t).state = some q → q < 17 ∧ q ≠ 14 ∧ q ≠ 15) :
    run (table continuation) c fuel = run base c fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have hp : ∀ t < fuel, ∀ q, (run base c t).state = some q → q < 17 ∧ q ≠ 14 ∧ q ≠ 15 := by
      intro t ht q hq
      exact hrows t (by omega) q hq
    simp only [run,ih hp]
    cases hc : run base c fuel with
    | mk left right state =>
      cases state with
      | none => rfl
      | some q =>
        have hq := hrows fuel (by omega) q (by simp [hc])
        have ht : Source284PayloadMarkOne.table continuation q (right.testBit 0) =
            Source284PayloadMarkOne.table sink q (right.testBit 0) := by
          have hsmall := hq.1
          interval_cases q <;> simp [Source284PayloadMarkOne.table]
        simp only [Nat.testBit_zero] at ht
        simp [step,table,hq.2.1,hq.2.2,base,ht]

/-- The reference marker is at its success return row exactly one step before
completion, with the new tape already reconstructed. -/
theorem mark_pre (xs ys : List Bool) (b c : Bool) (certificate tail : Nat) :
    run base ⟨certificate,2*zeros xs (flipped (b::c::ys) tail),some 0⟩ (4*xs.length+9) =
      ⟨2*zeros (xs++[b]) (flipped (c::ys) tail),certificate,some 14⟩ := by
  have ht : 4*xs.length+9 = 1+(2*xs.length+(7+(2*xs.length+1))) := by omega
  rw [ht,run_add _ _ 1 (2*xs.length+(7+(2*xs.length+1)))]
  change run (Source284PayloadMarkOne.table sink)
    (step (Source284PayloadMarkOne.table sink)
      ⟨certificate,2*zeros xs (flipped (b::c::ys) tail),some 0⟩) _ = _
  rw [Source284PayloadMarkOne.startup,run_add _ _ (2*xs.length) (7+(2*xs.length+1)),
    Source284PayloadMarkOne.forward_prefix]
  change run (Source284PayloadMarkOne.table sink) ⟨push (2*certificate+1) xs,
    bit b+2+4*(bit c+2+4*flipped ys tail),some 1⟩ _ = _
  rw [run_add _ _ 7 (2*xs.length+1),Source284PayloadMarkOne.found]
  change run (Source284PayloadMarkOne.table sink) ⟨bit b+4*(bit c+2+4*flipped ys tail),
    push (2*certificate+1) xs,some (8+5*0)⟩ _ = _
  rw [run_add _ _ (2*xs.length) 1,Source284PayloadMarkOne.back_prefix _ _ (by decide)]
  change step (Source284PayloadMarkOne.table sink)
    ⟨zeros xs (bit b+4*(bit c+2+4*flipped ys tail)),2*certificate+1,some 8⟩ = _
  simp [step,Source284PayloadMarkOne.table,Source284PayloadMarkOne.zeros_append,zeros,
    flipped,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod]
  omega

/-- The exhaustion return row is reached exactly one step before exiting. -/
theorem exhausted_pre (xs : List Bool) (certificate tail : Nat) :
    run base ⟨certificate,2*zeros xs (flipped [false] tail),some 0⟩ (4*xs.length+9) =
      ⟨2*zeros xs (flipped [false] tail),certificate,some 15⟩ := by
  have ht : 4*xs.length+9 = 1+(2*xs.length+(7+(2*xs.length+1))) := by omega
  rw [ht,run_add _ _ 1 (2*xs.length+(7+(2*xs.length+1)))]
  change run (Source284PayloadMarkOne.table sink)
    (step (Source284PayloadMarkOne.table sink)
      ⟨certificate,2*zeros xs (flipped [false] tail),some 0⟩) _ = _
  rw [Source284PayloadMarkOne.startup,run_add _ _ (2*xs.length) (7+(2*xs.length+1)),
    Source284PayloadMarkOne.forward_prefix]
  have he : flipped [false] tail = 2+16*tail := by simp [flipped,bit]; omega
  rw [he,run_add _ _ 7 (2*xs.length+1),Source284PayloadMarkOne.exhausted]
  change run (Source284PayloadMarkOne.table sink) ⟨2+16*tail,
    push (2*certificate+1) xs,some (8+5*1)⟩ _ = _
  rw [run_add _ _ (2*xs.length) 1,Source284PayloadMarkOne.back_prefix _ _ (by decide)]
  change step (Source284PayloadMarkOne.table sink) ⟨zeros xs (2+16*tail),2*certificate+1,some 13⟩ = _
  simp [step,Source284PayloadMarkOne.table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod]
  omega

theorem redirect_success (continuation : Nat → Bool → Row) (stream certificate : Nat) :
    step (table continuation) ⟨2*stream,certificate,some 14⟩ =
      ⟨certificate,2*stream,some 0⟩ := by
  simp [step,table,base,Source284PayloadMarkOne.table,bit,Nat.testBit_zero]
  split_ifs <;> omega

theorem redirect_exhaust (continuation : Nat → Bool → Row) (stream certificate : Nat) :
    step (table continuation) ⟨2*stream,certificate,some 15⟩ =
      ⟨certificate,2*stream,some 17⟩ := by
  simp [step,table,base,Source284PayloadMarkOne.table,bit,Nat.testBit_zero]
  split_ifs <;> omega

/-- One real payload pair is marked and the same table restarts. -/
theorem iteration (continuation : Nat → Bool → Row) (xs ys : List Bool)
    (b c : Bool) (certificate tail : Nat) :
    run (table continuation) ⟨certificate,2*zeros xs (flipped (b::c::ys) tail),some 0⟩
      (4*xs.length+10) =
      ⟨certificate,2*zeros (xs++[b]) (flipped (c::ys) tail),some 0⟩ := by
  let conf : Config := ⟨certificate,2*zeros xs (flipped (b::c::ys) tail),some 0⟩
  let limit := 4*xs.length+9
  have hv : Valid 19 conf := by intro q hq; simp [conf] at hq; subst q; omega
  have hp : run base conf limit = ⟨2*zeros (xs++[b]) (flipped (c::ys) tail),certificate,some 14⟩ :=
    mark_pre xs ys b c certificate tail
  have hf : (run base conf limit).state = some 14 := by rw [hp]
  have ha := run_agree continuation conf limit (avoid_before_final conf limit 14 hv (Or.inl rfl) hf)
  have ht : 4*xs.length+10 = limit+1 := by dsimp [limit]
  change run (table continuation) conf _ = _
  rw [ht,run,ha,hp,redirect_success]

/-- After the final real payload pair, the same table detects the sentinel
and enters the caller's continuation state zero. -/
theorem finish (continuation : Nat → Bool → Row) (xs : List Bool) (certificate tail : Nat) :
    run (table continuation) ⟨certificate,2*zeros xs (flipped [false] tail),some 0⟩
      (4*xs.length+10) = ⟨certificate,2*zeros xs (flipped [false] tail),some 17⟩ := by
  let conf : Config := ⟨certificate,2*zeros xs (flipped [false] tail),some 0⟩
  let limit := 4*xs.length+9
  have hv : Valid 19 conf := by intro q hq; simp [conf] at hq; subst q; omega
  have hp : run base conf limit = ⟨2*zeros xs (flipped [false] tail),certificate,some 15⟩ :=
    exhausted_pre xs certificate tail
  have hf : (run base conf limit).state = some 15 := by rw [hp]
  have ha := run_agree continuation conf limit (avoid_before_final conf limit 15 hv (Or.inr rfl) hf)
  have ht : 4*xs.length+10 = limit+1 := by dsimp [limit]
  change run (table continuation) conf _ = _
  rw [ht,run,ha,hp,redirect_exhaust]

/-- One iteration also works when the current payload bit is immediately
followed by the sentinel. -/
theorem iteration_rest (continuation : Nat → Bool → Row) (xs rest : List Bool)
    (b : Bool) (certificate tail : Nat) :
    run (table continuation)
      ⟨certificate,2*zeros xs (flipped ((b::rest)++[false]) tail),some 0⟩ (4*xs.length+10) =
      ⟨certificate,2*zeros (xs++[b]) (flipped (rest++[false]) tail),some 0⟩ := by
  cases rest with
  | nil => simpa using iteration continuation xs [] b false certificate tail
  | cons c ys => simpa using iteration continuation xs (ys++[false]) b c certificate tail

/-- Exact cost to mark `n` remaining pairs after `k` marked pairs and make
one final exhaustion scan. -/
def cost (k n : Nat) : Nat := (n+1)*(4*k+10)+2*n*(n+1)

theorem cost_zero (k : Nat) : cost k 0 = 4*k+10 := by simp [cost]

theorem cost_succ (k n : Nat) : cost k (n+1) = 4*k+10+cost (k+1) n := by
  unfold cost
  ring

/-- For any prepared marked prefix, the actual finite table autonomously
marks every remaining payload pair, detects the sentinel and enters the
continuation. The length appears only in the proved running-time bound. -/
theorem complete (continuation : Nat → Bool → Row) (xs ys : List Bool)
    (certificate tail : Nat) :
    run (table continuation) ⟨certificate,2*zeros xs (flipped (ys++[false]) tail),some 0⟩
      (cost xs.length ys.length) =
      ⟨certificate,2*zeros (xs++ys) (flipped [false] tail),some 17⟩ := by
  induction ys generalizing xs with
  | nil => simpa [cost_zero] using finish continuation xs certificate tail
  | cons b ys ih =>
    have ht : cost xs.length (b::ys).length = 4*xs.length+10+cost (xs++[b]).length ys.length := by
      simp only [List.length_cons,List.length_append,List.length_singleton]
      exact cost_succ xs.length ys.length
    rw [ht,run_add,iteration_rest,ih]
    simp [List.append_assoc]

theorem complete_unmarked (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail : Nat) :
    run (table continuation) ⟨certificate,2*flipped (w++[false]) tail,some 0⟩
      (2*w.length*w.length+12*w.length+10) =
      ⟨certificate,2*zeros w (flipped [false] tail),some 17⟩ := by
  have hc : cost 0 w.length = 2*w.length*w.length+12*w.length+10 := by
    unfold cost
    ring
  have h := complete continuation [] w certificate tail
  simpa [zeros,hc] using h

end Shared.Beeping.NPcoNP.Source284PayloadMarkLoop
