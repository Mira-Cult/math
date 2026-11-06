import Shared.Beeping.NPcoNP.Source284ScratchCompactMarked
import Shared.Beeping.NPcoNP.Source284ScratchShiftLoop

/-! A finite tape-controlled loop transfers zeros across the protected frame,
writing ones into the high scratch. It exits at the actual one sentinel. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284ScratchMarkedLoop

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped push)

abbrev sink := Source284ScratchShiftLoop.sink
def base : Nat → Bool → Row := Source284ScratchCompactMarked.table sink

/-- At the final return turn, the read tape bit is the next gap cell: zero
restarts the compacting pass; one hands off to the supplied continuation. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 13 then let r := base q b; ⟨r.write,r.turn,some (if b then 14 else 0)⟩
  else if q < 14 then base q b
  else shiftRow 14 (continuation (q-14) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (14+states) (table continuation) := by
  have hb := Source284ScratchCompactMarked.closed 1 sink (by decide) Source284ScratchShiftLoop.sink_closed
  intro q hq b q' hnext
  by_cases h13 : q = 13
  · subst q; cases b <;> simp [table] at hnext <;> omega
  · by_cases h14 : q < 14
    · have he : (base q b).next = some q' := by simpa [table,h13,h14] using hnext
      have h := hb q (by omega) b q' he
      omega
    · have ht : (shiftRow 14 (continuation (q-14) b)).next = some q' := by
        simpa [table,h13,h14] using hnext
      cases he : (continuation (q-14) b).next with
      | none => simp [shiftRow,he] at ht
      | some r =>
        have h := hv (q-14) (by omega) b r he
        simp [shiftRow,he] at ht
        subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (14+q) b = shiftRow 14 (continuation q b) := by
  simp [table,show 14+q ≠ 13 by omega,show ¬ 14+q < 14 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 14 c) = shiftConfig 14 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 14 c) fuel = shiftConfig 14 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem base_closed : Closed 15 base := by
  exact Source284ScratchCompactMarked.closed 1 sink (by decide) Source284ScratchShiftLoop.sink_closed

theorem final_rows : ∀ b, (base 13 b).next = some 14 := by decide +kernel

theorem sink_row (b : Bool) : base 14 b = ⟨b,false,some 14⟩ := by cases b <;> rfl

theorem sink_run (c : Config) (h : c.state = some 14) (fuel : Nat) :
    (run base c fuel).state = some 14 := by
  induction fuel with
  | zero => exact h
  | succ fuel ih =>
    cases hc : run base c fuel with
    | mk left right state =>
      simp only [hc] at ih
      subst state
      simp [run,hc,step,sink_row]

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

/-- The reference pass reaches the last return row after a positive finite
number of steps; the next read is exactly the gap/sentinel bit. -/
theorem compact_pre (w : List Bool) (certificate tail : Nat) :
    run base ⟨2*certificate,2*flipped w tail,some 0⟩ (8*w.length+10) =
      ⟨2*flipped w (2*tail+1),certificate,some 13⟩ := by
  have ht : 8*w.length+10 = (6*w.length)+(6+((2*w.length+3)+1)) := by omega
  unfold base
  rw [ht,run_add,Source284ScratchCompactMarked.payload_pairs,run_add]
  have he : 2*flipped [] tail = 8*tail := by simp [flipped]; omega
  rw [he,Source284ScratchCompactMarked.terminator,Source284ScratchCompactMarked.relocated_run]
  have ht2 : 2*w.length+3 = 3+2*w.length := by omega
  rw [ht2,run_add,run_add,Source284ScratchFlipReturn.turn_start,
    Source284ScratchFlipReturn.reverse_pairs,Source284ScratchFlipReturn.raw_flipped]
  change shiftConfig 8 (step (Source284ScratchFlipReturn.table sink)
    ⟨flipped w (2*tail+1),2*certificate,some 3⟩) = _
  simp [step,Source284ScratchFlipReturn.table,shiftConfig,bit,Nat.testBit_zero] <;> omega

theorem avoid_before_final (c : Config) (limit : Nat)
    (hfinal : (run base c limit).state = some 13) :
    ∀ t < limit, (run base c t).state ≠ some 13 ∧ (run base c t).state ≠ some 14 := by
  intro t ht
  constructor
  · intro hq
    have hs : (run base c (t+1)).state = some 14 := by
      simp only [run]
      exact final_step _ hq
    have h := sink_run (run base c (t+1)) hs (limit-(t+1))
    rw [← run_add] at h
    have he : t+1+(limit-(t+1)) = limit := by omega
    rw [he,hfinal] at h
    contradiction
  · intro hq
    have h := sink_run (run base c t) hq (limit-t)
    rw [← run_add] at h
    have he : t+(limit-t) = limit := by omega
    rw [he,hfinal] at h
    contradiction

theorem run_agree (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat)
    (hvalid : Valid 15 c)
    (hrows : ∀ t < fuel, (run base c t).state ≠ some 13 ∧ (run base c t).state ≠ some 14) :
    run (table continuation) c fuel = run base c fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have hp : ∀ t < fuel, (run base c t).state ≠ some 13 ∧ (run base c t).state ≠ some 14 := by
      intro t ht; exact hrows t (by omega)
    simp only [run,ih hp]
    cases hc : run base c fuel with
    | mk left right state =>
      cases state with
      | none => rfl
      | some q =>
        have hq : q < 15 := (valid_run 15 base c base_closed hvalid fuel) q (by simp [hc])
        have hn13 : q ≠ 13 := by intro he; subst q; exact (hrows fuel (by omega)).1 (by simp [hc])
        have hn14 : q ≠ 14 := by intro he; subst q; exact (hrows fuel (by omega)).2 (by simp [hc])
        have hl : q < 14 := by omega
        simp [step,table,hn13,hl]

theorem redirected_final (continuation : Nat → Bool → Row) (left certificate : Nat) :
    step (table continuation) ⟨2*left,certificate,some 13⟩ =
      ⟨certificate,2*left,some (if certificate%2 = 1 then 14 else 0)⟩ := by
  simp [step,table,base,Source284ScratchCompactMarked.table,Source284ScratchCompactOne.table,Source284ScratchFlipReturn.table,
    shiftRow,bit,Nat.testBit_zero]
  split <;> omega

theorem iteration (continuation : Nat → Bool → Row) (w : List Bool) (certificate tail : Nat) :
    run (table continuation) ⟨2*certificate,2*flipped w tail,some 0⟩ (8*w.length+11) =
      ⟨certificate,2*flipped w (2*tail+1),some (if certificate%2 = 1 then 14 else 0)⟩ := by
  let c : Config := ⟨2*certificate,2*flipped w tail,some 0⟩
  let limit := 8*w.length+10
  have hv : Valid 15 c := by intro q hq; simp [c] at hq; subst q; decide
  have hpre : run base c limit = ⟨2*flipped w (2*tail+1),certificate,some 13⟩ := compact_pre w certificate tail
  have hf : (run base c limit).state = some 13 := by rw [hpre]
  have heq := run_agree continuation c limit hv (avoid_before_final c limit hf)
  have ht : 8*w.length+11 = limit+1 := by dsimp [limit]
  change run (table continuation) c _ = _
  rw [ht,run,heq,hpre,redirected_final]

def marks : Nat → Nat → Nat
  | 0, tail => tail
  | n+1, tail => marks n (2*tail+1)

/-- The finite table consumes every zero in the actual gap, stopping when it
reads the existing one sentinel. Each removed zero creates one scratch mark. -/
theorem countdown (continuation : Nat → Bool → Row) (count : Nat) (w : List Bool)
    (input tail : Nat) :
    run (table continuation) ⟨2^(count+1)*(2*input+1),2*flipped w tail,some 0⟩
      ((count+1)*(8*w.length+11)) =
      ⟨2*input+1,2*flipped w (marks (count+1) tail),some 14⟩ := by
  induction count generalizing tail with
  | zero =>
    have h := iteration continuation w (2*input+1) tail
    simpa [marks,Nat.add_mod,Nat.mul_mod] using h
  | succ count ih =>
    have hpow : 2^(count+1+1)*(2*input+1) = 2*(2^(count+1)*(2*input+1)) := by
      rw [pow_succ]; ring
    have ht : (count+1+1)*(8*w.length+11) = (8*w.length+11)+(count+1)*(8*w.length+11) := by ring
    have heven : (2^(count+1)*(2*input+1))%2 ≠ 1 := by
      rw [pow_succ]
      simp [Nat.mul_mod]
    rw [hpow,ht,run_add,iteration]
    simp only [heven,↓reduceIte]
    rw [ih]
    rfl

/-- Once the sentinel is reached the finite continuation runs for every
subsequent clock, with the complete input and witness data retained. -/
theorem countdown_after (continuation : Nat → Bool → Row) (count : Nat) (w : List Bool)
    (input tail fuel : Nat) :
    run (table continuation) ⟨2^(count+1)*(2*input+1),2*flipped w tail,some 0⟩
      ((count+1)*(8*w.length+11)+fuel) =
    shiftConfig 14 (run continuation
      ⟨2*input+1,2*flipped w (marks (count+1) tail),some 0⟩ fuel) := by
  rw [run_add,countdown]
  change run (table continuation) (shiftConfig 14
    ⟨2*input+1,2*flipped w (marks (count+1) tail),some 0⟩) fuel = _
  rw [relocated_run]

namespace Fixtures
example (continuation : Nat → Bool → Row) :
    run (table continuation) ⟨28,150,some 0⟩ 54 = ⟨7,918,some 14⟩ := by
  simpa [marks,flipped,bit] using countdown continuation 1 [true,false] 3 1

example (continuation : Nat → Bool → Row) :
    run (table continuation) ⟨14,0,some 0⟩ 11 = ⟨7,8,some 14⟩ := by
  simpa [marks,flipped] using countdown continuation 0 [] 3 0
end Fixtures
end Shared.Beeping.NPcoNP.Source284ScratchMarkedLoop
