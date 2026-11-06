import Shared.Beeping.NPcoNP.Source284LengthEqualPre
import Shared.Beeping.NPcoNP.Source284LengthGrowTime

/-! Both the restart and the equality handoff are real finite table rows. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284LengthGrowContinue

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig shiftRow)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284LengthGrowRound
open Shared.Beeping.NPcoNP.Source284LengthGrowPre
open Shared.Beeping.NPcoNP.Source284LengthEqualPre
open Shared.Beeping.NPcoNP.Source284LengthGrowLoop (totalTime quarters)

def base : Nat → Bool → Row := Source284LengthGrowRound.table

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 98 then let r := base q b; ⟨r.write,r.turn,some 0⟩
  else if q = 117 then let r := base q b; ⟨r.write,r.turn,some 119⟩
  else if q < 119 then base q b
  else shiftRow 119 (continuation (q-119) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (119+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases h98 : q = 98
  · subst q; simp [table] at hnext; omega
  · by_cases h117 : q = 117
    · subst q; simp [table] at hnext; omega
    · by_cases hs : q < 119
      · have h := Source284LengthGrowRound.closed q hs b q'
        have hb : (Source284LengthGrowRound.table q b).next = some q' := by
          simpa [table,h98,h117,hs,base] using hnext
        have hr := h hb
        omega
      · have h : (shiftRow 119 (continuation (q-119) b)).next = some q' := by
          simpa [table,h98,h117,hs] using hnext
        cases he : (continuation (q-119) b).next with
        | none => simp [shiftRow,he] at h
        | some r =>
          have hr := hv (q-119) (by omega) b r he
          simp [shiftRow,he] at h
          subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (119+q) b = shiftRow 119 (continuation q b) := by
  simp [table,show 119+q ≠ 98 by omega,show 119+q ≠ 117 by omega,
    show ¬ 119+q < 119 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 119 c) = shiftConfig 119 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 119 c) fuel = shiftConfig 119 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

def returnRow (q : Nat) : Prop := q = 98 ∨ q = 117
def sinkIndex (q : Nat) : Nat := if q = 98 then 99 else 118

theorem sink_row (q : Nat) (hq : q = 99 ∨ q = 118) (b : Bool) :
    base q b = ⟨b,false,some q⟩ := by
  rcases hq with rfl | rfl <;> cases b <;> rfl

theorem sink_step (c : Config) (q : Nat) (hq : q = 99 ∨ q = 118)
    (h : c.state = some q) : (step base c).state = some q := by
  cases c with
  | mk left right state =>
    simp only at h
    subst state
    simp [step,sink_row q hq]

theorem sink_run (c : Config) (q : Nat) (hq : q = 99 ∨ q = 118)
    (h : c.state = some q) (fuel : Nat) : (run base c fuel).state = some q := by
  induction fuel with
  | zero => exact h
  | succ fuel ih => exact sink_step _ q hq ih

theorem final_step (c : Config) (q : Nat) (hq : returnRow q)
    (h : c.state = some q) : (step base c).state = some (sinkIndex q) := by
  cases c with
  | mk left right state =>
    simp only at h
    subst state
    rcases hq with rfl | rfl <;>
      simp [step,base,Source284LengthGrowRound.table,Source284MatchLoop.table,
        Source284MatchStep.table,Source284UnaryMarkOne.table,Source284MatchDispatch.table,
        Source284LengthGrowRound.dispatch,Source284LengthGrowRound.grow,Source284LengthGrowRound.equal,
        Source284MatchReset.table,Source284UnaryClear.table,Source284PayloadReset.table,
        Source284ScratchShiftCycle.repeatTable,Source284ScratchShiftCycle.table,
        Source284ScratchShiftPipeline.entry,Source284ScratchShift.table,
        Source284ScratchShiftReturn.table,Source284ScratchFlipReturn.table,shiftRow,sinkIndex]

theorem avoid_before (c : Config) (limit final : Nat) (hvalid : Valid 119 c)
    (hfinal : returnRow final) (hfinish : (run base c limit).state = some final) :
    ∀ t < limit, ∀ q, (run base c t).state = some q → q < 119 ∧ ¬returnRow q := by
  intro t ht q hq
  have hbound := (valid_run 119 base c Source284LengthGrowRound.closed hvalid t) q hq
  refine ⟨hbound,?_⟩
  intro hret
  have hn : (run base c (t+1)).state = some (sinkIndex q) := by
    simp only [run]
    exact final_step _ q hret hq
  have hs : sinkIndex q = 99 ∨ sinkIndex q = 118 := by
    rcases hret with rfl | rfl <;> simp [sinkIndex]
  have h := sink_run (run base c (t+1)) (sinkIndex q) hs hn (limit-(t+1))
  rw [← run_add] at h
  have he : t+1+(limit-(t+1)) = limit := by omega
  rw [he,hfinish] at h
  have heq : final = sinkIndex q := Option.some.inj h
  rcases hfinal with rfl | rfl <;> rcases hs with hs | hs <;> omega

theorem run_agree (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat)
    (hrows : ∀ t < fuel, ∀ q, (run base c t).state = some q → q < 119 ∧ ¬returnRow q) :
    run (table continuation) c fuel = run base c fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have hp : ∀ t < fuel, ∀ q, (run base c t).state = some q → q < 119 ∧ ¬returnRow q := by
      intro t ht q hq
      exact hrows t (by omega) q hq
    simp only [run,ih hp]
    cases hc : run base c fuel with
    | mk left right state =>
      cases state with
      | none => rfl
      | some q =>
        have hq := hrows fuel (by omega) q (by simp [hc])
        have h98 : q ≠ 98 := by intro h; exact hq.2 (Or.inl h)
        have h117 : q ≠ 117 := by intro h; exact hq.2 (Or.inr h)
        simp [step,table,h98,h117,hq.1]

theorem grow_step (continuation : Nat → Bool → Row) (xs rest : List Bool) (b : Bool)
    (certificate tail : Nat) :
    run (table continuation) ⟨pairTape (List.replicate xs.length false) certificate,
      2*flipped ((xs++b::rest)++[false]) tail,some 0⟩ (growTime xs rest b) =
    ⟨pairTape (List.replicate (xs.length+1) false) certificate,
      2*flipped ((xs++b::rest)++[false]) (tail/4),some 0⟩ := by
  let c : Config := ⟨pairTape (List.replicate xs.length false) certificate,
      2*flipped ((xs++b::rest)++[false]) tail,some 0⟩
  let t := roundPreTime xs rest b
  have hv : Valid 119 c := by intro q hq; simp [c] at hq; omega
  have hp : run base c t = ⟨2*flipped ((xs++b::rest)++[false]) (tail/4),
      pairTape (List.replicate (xs.length+1) false) certificate,some 98⟩ :=
    grow_round_pre xs rest b certificate tail
  have hf : (run base c t).state = some 98 := by rw [hp]
  have ha := run_agree continuation c t (avoid_before c t 98 hv (Or.inl rfl) hf)
  rw [← preTime_succ,run_add,ha,hp]
  simp [run,step,table,base,Source284LengthGrowRound.table,Source284MatchLoop.table,
    Source284MatchStep.table,Source284UnaryMarkOne.table,Source284MatchDispatch.table,
    Source284LengthGrowRound.dispatch,Source284LengthGrowRound.grow,
    Source284MatchReset.table,Source284UnaryClear.table,Source284PayloadReset.table,
    Source284ScratchShiftCycle.repeatTable,Source284ScratchShiftCycle.table,
    Source284ScratchShiftPipeline.entry,Source284ScratchShift.table,
    Source284ScratchShiftReturn.table,Source284ScratchFlipReturn.table,shiftRow,bit,
    Nat.testBit_zero] <;> split_ifs <;> omega

theorem equal_step (continuation : Nat → Bool → Row) (w : List Bool) (certificate tail : Nat) :
    run (table continuation) ⟨pairTape (List.replicate w.length false) certificate,
      2*flipped (w++[false]) tail,some 0⟩ (equalTime w.length) =
    ⟨pairTape (List.replicate w.length false) certificate,
      2*flipped (w++[false]) tail,some 119⟩ := by
  let c : Config := ⟨pairTape (List.replicate w.length false) certificate,
    2*flipped (w++[false]) tail,some 0⟩
  let t := equalPreTime w.length
  have hv : Valid 119 c := by intro q hq; simp [c] at hq; omega
  have hp : run base c t = ⟨2*flipped (w++[false]) tail,
      pairTape (List.replicate w.length false) certificate,some 117⟩ :=
    equal_round_pre w certificate tail
  have hf : (run base c t).state = some 117 := by rw [hp]
  have ha := run_agree continuation c t (avoid_before c t 117 hv (Or.inr rfl) hf)
  rw [← equalPreTime_succ,run_add,ha,hp]
  simp [run,step,table,base,Source284LengthGrowRound.table,Source284MatchLoop.table,
    Source284MatchStep.table,Source284UnaryMarkOne.table,Source284MatchDispatch.table,
    Source284LengthGrowRound.dispatch,Source284LengthGrowRound.equal,
    Source284MatchReset.table,Source284UnaryClear.table,Source284PayloadReset.table,
    Source284ScratchFlipReturn.table,shiftRow,bit,Nat.testBit_zero] <;> split_ifs <;> omega

theorem produce (continuation : Nat → Bool → Row) (xs rest : List Bool)
    (certificate tail : Nat) :
    run (table continuation) ⟨pairTape (List.replicate xs.length false) certificate,
      2*flipped ((xs++rest)++[false]) tail,some 0⟩ (totalTime xs rest) =
    ⟨pairTape (List.replicate (xs++rest).length false) certificate,
      2*flipped ((xs++rest)++[false]) (quarters rest.length tail),some 119⟩ := by
  induction rest generalizing xs tail with
  | nil => simpa [totalTime,quarters] using equal_step continuation xs certificate tail
  | cons b rest ih =>
    rw [totalTime,run_add,grow_step]
    have h := ih (xs++[b]) (tail/4)
    simpa only [List.append_assoc,List.singleton_append,List.length_append,
      List.length_singleton,List.length_cons,List.length_nil,Nat.zero_add,quarters] using h

/-- The caller's finite table executes immediately after length generation,
with no preloaded control state and no omitted transition. -/
theorem produce_then (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail fuel : Nat) :
    run (table continuation) ⟨pairTape [] certificate,2*flipped (w++[false]) tail,some 0⟩
      (totalTime [] w+fuel) =
    shiftConfig 119 (run continuation ⟨pairTape (List.replicate w.length false) certificate,
      2*flipped (w++[false]) (quarters w.length tail),some 0⟩ fuel) := by
  have h := produce continuation [] w certificate tail
  simp only [List.length_nil,List.replicate_zero,List.nil_append] at h
  rw [run_add,h]
  change run (table continuation) (shiftConfig 119 ⟨pairTape (List.replicate w.length false) certificate,
    2*flipped (w++[false]) (quarters w.length tail),some 0⟩) fuel = _
  exact relocated_run continuation _ fuel

end Shared.Beeping.NPcoNP.Source284LengthGrowContinue
