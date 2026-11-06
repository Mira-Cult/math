import Shared.Beeping.NPcoNP.Source284LengthGrowPre

/-! Autonomous input-length token generation from an empty prepared token
sentinel and framed scratch input. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284LengthGrowLoop

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284LengthGrowRound
open Shared.Beeping.NPcoNP.Source284LengthGrowPre

def base : Nat → Bool → Row := Source284LengthGrowRound.table

/-- The last turn of a successful growth restarts comparison. Its write and
movement are unchanged; the equality branch remains distinct. -/
def table (q : Nat) (b : Bool) : Row :=
  if q = 98 then let r := base q b; ⟨r.write,r.turn,some 0⟩ else base q b

theorem closed : Closed 119 table := by
  intro q hq b q' hnext
  by_cases h : q = 98
  · simp [table,h] at hnext
    omega
  · apply Source284LengthGrowRound.closed q hq b q'
    simpa [table,h,base] using hnext

theorem sink_row (b : Bool) : base 99 b = ⟨b,false,some 99⟩ := by
  cases b <;> rfl

theorem sink_step (c : Config) (h : c.state = some 99) : (step base c).state = some 99 := by
  cases c with
  | mk left right state =>
    simp only at h
    subst state
    simp [step,sink_row]

theorem sink_run (c : Config) (h : c.state = some 99) (fuel : Nat) :
    (run base c fuel).state = some 99 := by
  induction fuel with
  | zero => exact h
  | succ fuel ih => exact sink_step _ ih

theorem final_step (c : Config) (h : c.state = some 98) : (step base c).state = some 99 := by
  cases c with
  | mk left right state =>
    simp only at h
    subst state
    simp [step,base,Source284LengthGrowRound.table,Source284MatchLoop.table,
      Source284MatchStep.table,Source284UnaryMarkOne.table,Source284MatchDispatch.table,
      Source284PayloadMarkLoop.table,Source284PayloadMarkOne.table,
      Source284LengthGrowRound.dispatch,Source284LengthGrowRound.grow,
      Source284MatchReset.table,Source284UnaryClear.table,Source284PayloadReset.table,
      Source284ScratchShiftCycle.repeatTable,Source284ScratchShiftCycle.table,
      Source284ScratchShiftPipeline.entry,Source284ScratchShift.table,
      Source284ScratchShiftReturn.table,Source284ScratchFlipReturn.table,
      Source284HardwireTable.shiftRow]

/-- Reaching any non-sink final state proves that the redirected growth row
was not encountered earlier: its next reference state is absorbing. -/
theorem avoid_before (c : Config) (limit final : Nat) (hfinal : final ≠ 99)
    (hfinish : (run base c limit).state = some final) :
    ∀ t < limit, (run base c t).state ≠ some 98 := by
  intro t ht hq
  have hn : (run base c (t+1)).state = some 99 := by
    simp only [run]
    exact final_step _ hq
  have h := sink_run (run base c (t+1)) hn (limit-(t+1))
  rw [← run_add] at h
  have he : t+1+(limit-(t+1)) = limit := by omega
  rw [he,hfinish] at h
  exact hfinal (Option.some.inj h)

theorem run_agree (c : Config) (fuel : Nat)
    (hrows : ∀ t < fuel, (run base c t).state ≠ some 98) :
    run table c fuel = run base c fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have hp : ∀ t < fuel, (run base c t).state ≠ some 98 := by
      intro t ht
      exact hrows t (by omega)
    simp only [run,ih hp]
    cases hc : run base c fuel with
    | mk left right state =>
      cases state with
      | none => rfl
      | some q =>
        have hq : q ≠ 98 := by
          intro he; subst q
          exact hrows fuel (by omega) (by simp [hc])
        simp [step,table,hq]

/-- One strictly positive comparison/reset/growth cycle returns to state zero. -/
theorem grow_step (xs rest : List Bool) (b : Bool) (certificate tail : Nat) :
    run table ⟨pairTape (List.replicate xs.length false) certificate,
      2*flipped ((xs++b::rest)++[false]) tail,some 0⟩ (growTime xs rest b) =
    ⟨pairTape (List.replicate (xs.length+1) false) certificate,
      2*flipped ((xs++b::rest)++[false]) (tail/4),some 0⟩ := by
  let c : Config := ⟨pairTape (List.replicate xs.length false) certificate,
      2*flipped ((xs++b::rest)++[false]) tail,some 0⟩
  let t := roundPreTime xs rest b
  have hp : run base c t = ⟨2*flipped ((xs++b::rest)++[false]) (tail/4),
      pairTape (List.replicate (xs.length+1) false) certificate,some 98⟩ :=
    grow_round_pre xs rest b certificate tail
  have hf : (run base c t).state = some 98 := by rw [hp]
  have ha := run_agree c t (avoid_before c t 98 (by decide) hf)
  rw [← preTime_succ,run_add,ha,hp]
  simp [run,step,table,base,Source284LengthGrowRound.table,Source284MatchLoop.table,
    Source284MatchStep.table,Source284UnaryMarkOne.table,Source284MatchDispatch.table,
    Source284PayloadMarkLoop.table,Source284PayloadMarkOne.table,
    Source284LengthGrowRound.dispatch,Source284LengthGrowRound.grow,
    Source284MatchReset.table,Source284UnaryClear.table,Source284PayloadReset.table,
    Source284ScratchShiftCycle.repeatTable,Source284ScratchShiftCycle.table,
    Source284ScratchShiftPipeline.entry,Source284ScratchShift.table,
    Source284ScratchShiftReturn.table,Source284ScratchFlipReturn.table,
    Source284HardwireTable.shiftRow,bit,Nat.testBit_zero] <;> split_ifs <;> omega

theorem equal_step (w : List Bool) (certificate tail : Nat) :
    run table ⟨pairTape (List.replicate w.length false) certificate,
      2*flipped (w++[false]) tail,some 0⟩ (equalTime w.length) =
    ⟨pairTape (List.replicate w.length false) certificate,
      2*flipped (w++[false]) tail,some 118⟩ := by
  let c : Config := ⟨pairTape (List.replicate w.length false) certificate,
    2*flipped (w++[false]) tail,some 0⟩
  have hp : run base c (equalTime w.length) =
      ⟨pairTape (List.replicate w.length false) certificate,
        2*flipped (w++[false]) tail,some 118⟩ := equal_round w certificate tail
  have hf : (run base c (equalTime w.length)).state = some 118 := by rw [hp]
  rw [run_agree c _ (avoid_before c _ 118 (by decide) hf),hp]

/-- Runtime is a proof of how long the fixed table runs, not a value supplied
as a stopping command. -/
def totalTime (xs rest : List Bool) : Nat :=
  match rest with
  | [] => equalTime xs.length
  | b::bs => growTime xs bs b + totalTime (xs++[b]) bs
termination_by rest.length

def quarters : Nat → Nat → Nat
  | 0, tail => tail
  | n+1, tail => quarters n (tail/4)

/-- Starting with one unmarked token for each already-accounted payload bit,
the fixed table autonomously reaches equality and produces one token for each
remaining payload bit. -/
theorem produce (xs rest : List Bool) (certificate tail : Nat) :
    run table ⟨pairTape (List.replicate xs.length false) certificate,
      2*flipped ((xs++rest)++[false]) tail,some 0⟩ (totalTime xs rest) =
    ⟨pairTape (List.replicate (xs++rest).length false) certificate,
      2*flipped ((xs++rest)++[false]) (quarters rest.length tail),some 118⟩ := by
  induction rest generalizing xs tail with
  | nil => simpa [totalTime,quarters] using equal_step xs certificate tail
  | cons b rest ih =>
    rw [totalTime,run_add,grow_step]
    have h := ih (xs++[b]) (tail/4)
    simpa only [List.append_assoc,List.singleton_append,List.length_append,
      List.length_singleton,List.length_cons,List.length_nil,Nat.zero_add,quarters] using h

/-- The common initial case has no unary tokens; the output length is exactly
the payload length, including the zero-length case. -/
theorem produce_from_zero (w : List Bool) (certificate tail : Nat) :
    run table ⟨pairTape [] certificate,2*flipped (w++[false]) tail,some 0⟩
      (totalTime [] w) =
    ⟨pairTape (List.replicate w.length false) certificate,
      2*flipped (w++[false]) (quarters w.length tail),some 118⟩ := by
  simpa using produce [] w certificate tail

end Shared.Beeping.NPcoNP.Source284LengthGrowLoop
