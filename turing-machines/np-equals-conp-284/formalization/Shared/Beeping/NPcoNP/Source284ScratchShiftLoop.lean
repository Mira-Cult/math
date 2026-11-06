import Shared.Beeping.NPcoNP.Source284ScratchShiftCycle

/-! One fixed finite source table redirects the shift-and-return cycle's last
transition back to its start. It has no stopping condition; this is a runtime
loop primitive, not yet a bounded pair loader or a beeping machine. -/
namespace Shared.Beeping.NPcoNP.Source284ScratchShiftLoop

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (push flipped)
open Shared.Beeping.NPcoNP.Source284Parser (payloadFold)
open Shared.Beeping.NPcoNP.Source284ScratchShift (written)

def sink (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
def base : Nat → Bool → Row := Source284ScratchShiftCycle.table sink

/-- State 13 is the reverse scanner's final turn. Redirecting its next state
preserves its actual write and move and starts the next cycle. -/
def table (q : Nat) (b : Bool) : Row :=
  if q = 13 then let r := base q b; ⟨r.write,r.turn,some 0⟩ else base q b

/-- All rows of the fixed loop stay within its 14 logical states. -/
theorem finite_row_closed : ∀ q : Fin 14, ∀ b : Bool,
    (table q.val b).next.getD 0 < 14 := by decide +kernel

theorem closed : Closed 14 table := by
  intro q hq b q' hnext
  have h := finite_row_closed ⟨q,hq⟩ b
  simp [hnext] at h
  exact h

/-- Every in-range row has a continuing successor. -/
theorem finite_row_continues : ∀ q : Fin 14, ∀ b : Bool,
    (table q.val b).next.isSome = true := by decide +kernel

theorem step_continues (c : Config) (hvalid : Valid 14 c)
    (hactive : c.state.isSome = true) : (step table c).state.isSome = true := by
  cases c with
  | mk left right state =>
    cases state with
    | none => simp at hactive
    | some q =>
      have hq : q < 14 := hvalid q rfl
      have hn := finite_row_continues ⟨q,hq⟩ (right.testBit 0)
      simp only [Nat.testBit_zero] at hn
      cases he : (table q (decide (right % 2 = 1))).next with
      | none => simp [he] at hn
      | some r =>
        simp [step,Nat.testBit_zero,he]
        split <;> simp [he]

/-- The loop executes without entering the source model's accepting state
at every finite time, not merely at the sampled cycle boundaries. -/
theorem run_continues (c : Config) (hvalid : Valid 14 c)
    (hactive : c.state.isSome = true) (fuel : Nat) :
    (run table c fuel).state.isSome = true := by
  induction fuel with
  | zero => exact hactive
  | succ fuel ih =>
    exact step_continues _ (valid_run 14 table c closed hvalid fuel) ih

theorem sink_closed : Closed 1 sink := by
  intro q hq b q' h
  simp [sink] at h
  omega

theorem base_closed : Closed 15 base := by
  have h := Source284ScratchShiftCycle.closed 1 sink (by decide) sink_closed
  simpa [base] using h

/-- Finite row facts for the actual 14-state prefix and its reference sink. -/
theorem final_rows : ∀ b, (base 13 b).next = some 14 := by decide +kernel

theorem sink_row (b : Bool) : base 14 b = ⟨b,false,some 14⟩ := by
  cases b <;> rfl

theorem sink_step (c : Config) (h : c.state = some 14) :
    (step base c).state = some 14 := by
  cases c with
  | mk left right state =>
    simp only at h
    subst state
    simp [step,sink_row]

theorem sink_run (c : Config) (h : c.state = some 14) (fuel : Nat) :
    (run base c fuel).state = some 14 := by
  induction fuel with
  | zero => exact h
  | succ fuel ih => exact sink_step _ ih

theorem final_step (c : Config) (h : c.state = some 13) :
    (step base c).state = some 14 := by
  cases c with
  | mk left right state =>
    simp only at h
    subst state
    have hr := final_rows (right.testBit 0)
    simp only [Nat.testBit_zero] at hr
    simp [step,hr]
    split <;> simp [hr]

/-- Just before the last turn, the scanner has crossed the entire shifted
stream and stands next to the preserved certificate. -/
theorem return_pre (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail : Nat) :
    run (Source284ScratchShiftReturn.table continuation)
      ⟨2*(tail/2),payloadFold (2*certificate) (written false w),some 0⟩ (2*w.length+2) =
      ⟨2*flipped w (tail/2),2*certificate,some 6⟩ := by
  rw [Source284ScratchShiftReturn.fold_written]
  have ht : 2*w.length+2 = 1+(2*w.length+1) := by omega
  rw [ht,Source284PayloadPop.run_add]
  change run (Source284ScratchShiftReturn.table continuation)
    (step (Source284ScratchShiftReturn.table continuation)
      ⟨2*(tail/2),2*push (4*certificate) w,some 0⟩) _ = _
  rw [Source284ScratchShiftReturn.entry_step]
  have he : 2*(2*(tail/2)) = 4*(tail/2) := by omega
  rw [he]
  change run (Source284ScratchShiftReturn.table continuation)
    (shiftConfig 1 ⟨4*(tail/2),push (4*certificate) w,some 3⟩) _ = _
  rw [Source284ScratchShiftReturn.relocated_run]
  have hc : 2*w.length+1 = (2*w.length)+1 := by omega
  rw [hc,Source284ScratchFlipReturn.run_add,Source284ScratchFlipReturn.reverse_pairs,
    Source284ScratchFlipReturn.raw_flipped]
  change shiftConfig 1 (step (Source284ScratchFlipReturn.table continuation)
    ⟨flipped w (tail/2),4*certificate,some 3⟩) = _
  simp [step,Source284ScratchFlipReturn.table,shiftConfig,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega

/-- The exact base configuration one step before a completed cycle. -/
theorem cycle_pre (w : List Bool) (certificate tail : Nat) :
    run base ⟨certificate,2*flipped w tail,some 0⟩ (4*w.length+6) =
      ⟨2*flipped w (tail/2),2*certificate,some 13⟩ := by
  have ht : 4*w.length+6 = (2*w.length+4)+(2*w.length+2) := by omega
  rw [ht,Source284PayloadPop.run_add]
  change run (Source284ScratchShiftPipeline.entry (Source284ScratchShiftReturn.table sink))
    (run (Source284ScratchShiftPipeline.entry (Source284ScratchShiftReturn.table sink)) _ _) _ = _
  rw [Source284ScratchShiftPipeline.shift_entry]
  change run (Source284ScratchShiftPipeline.entry (Source284ScratchShiftReturn.table sink))
    (shiftConfig 1 (shiftConfig 6 ⟨2*(tail/2),payloadFold (2*certificate) (written false w),some 0⟩)) _ = _
  rw [Source284ScratchShiftPipeline.relocated_run,Source284ScratchShift.relocated_run,return_pre]
  rfl

/-- No earlier step visits the redirected row: visiting it would enter the
absorbing reference sink and could not reach the stated pre-final state. -/
theorem avoid_before_final (c : Config) (limit : Nat)
    (hfinal : (run base c limit).state = some 13) :
    ∀ t < limit, (run base c t).state ≠ some 13 := by
  intro t ht hq
  have hs : (run base c (t+1)).state = some 14 := by
    simp only [run]
    exact final_step _ hq
  have h := sink_run (run base c (t+1)) hs (limit-(t+1))
  rw [← Source284PayloadPop.run_add] at h
  have he : t+1+(limit-(t+1)) = limit := by omega
  rw [he,hfinal] at h
  contradiction

theorem run_agree (c : Config) (fuel : Nat)
    (hrows : ∀ t < fuel, (run base c t).state ≠ some 13) :
    run table c fuel = run base c fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have hp : ∀ t < fuel, (run base c t).state ≠ some 13 := by
      intro t ht
      exact hrows t (by omega)
    simp only [run,ih hp]
    cases hc : run base c fuel with
    | mk left right state =>
      cases state with
      | none => rfl
      | some q =>
        have hq : q ≠ 13 := by
          intro he
          subst q
          exact hrows fuel (by omega) (by simp [hc])
        simp [step,table,hq]

theorem redirected_final (left certificate : Nat) :
    step table ⟨2*left,2*certificate,some 13⟩ = ⟨2*certificate,2*left,some 0⟩ := by
  simp [step,table,base,Source284ScratchShiftCycle.table,Source284ScratchShiftPipeline.entry,
    Source284ScratchShift.table,Source284ScratchShiftReturn.table,Source284ScratchFlipReturn.table,
    Source284HardwireTable.shiftRow,bit,Nat.testBit_zero]

/-- The same 14-state table completes one shift and returns to state zero. -/
theorem iteration (w : List Bool) (certificate tail : Nat) :
    run table ⟨certificate,2*flipped w tail,some 0⟩ (4*w.length+7) =
      ⟨2*certificate,2*flipped w (tail/2),some 0⟩ := by
  let c : Config := ⟨certificate,2*flipped w tail,some 0⟩
  let limit := 4*w.length+6
  have hpre : run base c limit = ⟨2*flipped w (tail/2),2*certificate,some 13⟩ :=
    cycle_pre w certificate tail
  have hf : (run base c limit).state = some 13 := by rw [hpre]
  have heq := run_agree c limit (avoid_before_final c limit hf)
  have ht : 4*w.length+7 = limit+1 := by dsimp [limit]
  change run table c _ = _
  rw [ht,run,heq,hpre,redirected_final]

/-- One fixed table supports arbitrarily many cycles. The step count in the
statement is a proof index; no machine-side counter or stopping test is used. -/
theorem iterations (count : Nat) (w : List Bool) (certificate tail : Nat) :
    run table ⟨certificate,2*flipped w tail,some 0⟩ (count*(4*w.length+7)) =
      ⟨2^count*certificate,2*flipped w (tail/2^count),some 0⟩ := by
  induction count generalizing certificate tail with
  | zero => simp [run]
  | succ count ih =>
    have ht : (count+1)*(4*w.length+7) = (4*w.length+7)+count*(4*w.length+7) := by ring
    rw [ht,Source284PayloadPop.run_add,iteration,ih]
    have hm : 2^count*(2*certificate) = 2^(count+1)*certificate := by rw [pow_succ]; ring
    have hd : (tail/2)/2^count = tail/2^(count+1) := by
      rw [Nat.div_div_eq_div_mul,pow_succ]
      congr 1
      ring
    rw [hm,hd]

end Shared.Beeping.NPcoNP.Source284ScratchShiftLoop
