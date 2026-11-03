import Shared.Beeping.NPcoNP.Source284EvaluatorPackedStep
import Shared.PNP.Record285.CandidateNumericStep
import Shared.ComplexityBridge.TM2UnaryIterate

/-! A charged choice-aware step for the selected reference evaluator.
The auxiliary 284 step reads the next choice in place of the current cell;
adding twice that cell to the control selects the same 285 unary row. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ReferenceChoiceStep
open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP
open Shared.Beeping.NPcoNP.Source284EvaluatorPackedStep
open Shared.Beeping.NPcoNP.Source284EvaluatorBitStep
open Shared.Beeping.NPcoNP.Source284RecordBitCost
open Shared.Beeping.NPcoNP.Source284UnaryCountBits
open Shared.Codes.BitNumeralCompare (value)
open Shared.PNP.Record285.RelativeTape

abbrev Bits := List Bool
abbrev Input := Packed × Bits

def base (p : Input) : Packed := p.1
def choices (p : Input) : Bits := p.2
def extraState (p : Input) : Bits :=
  if read (base p) then incrementData (incrementData (state (base p))) else state (base p)
def newRight (p : Input) : Bits := (choices p).headD false :: (right (base p)).tail
def prepared (p : Input) : Packed :=
  ((code (base p),(left (base p),newRight p)),extraState p)
def nextChoices (p : Input) : Bits := (choices p).tail

def step (p : Input) : Input :=
  if zero (base p) then p else (Source284EvaluatorPackedStep.step (prepared p),nextChoices p)

theorem step_isPolyTime : ComplexityTheory.IsPolyTime step := by
  have hb : ComplexityTheory.IsPolyTime base := TM2PairFirst.first_isPolyTime
  have hch : ComplexityTheory.IsPolyTime choices := TM2GuardAllStep.second_isPolyTime
  have hc : ComplexityTheory.IsPolyTime (fun p : Input => code (base p)) :=
    TM2Compose.isPolyTime_comp base code hb (by
      exact TM2Compose.isPolyTime_comp (fun p : Packed => p.1) (fun p : Context => p.1)
        TM2PairFirst.first_isPolyTime TM2PairFirst.first_isPolyTime)
  have ht : ComplexityTheory.IsPolyTime (fun p : Input => tapes (base p)) :=
    TM2Compose.isPolyTime_comp base tapes hb (by
      exact TM2Compose.isPolyTime_comp (fun p : Packed => p.1) (fun p : Context => p.2)
        TM2PairFirst.first_isPolyTime TM2GuardAllStep.second_isPolyTime)
  have hl : ComplexityTheory.IsPolyTime (fun p : Input => left (base p)) :=
    TM2Compose.isPolyTime_comp (fun p : Input => tapes (base p)) (fun p : Bits × Bits => p.1) ht TM2PairFirst.first_isPolyTime
  have hr : ComplexityTheory.IsPolyTime (fun p : Input => right (base p)) :=
    TM2Compose.isPolyTime_comp (fun p : Input => tapes (base p)) (fun p : Bits × Bits => p.2) ht TM2GuardAllStep.second_isPolyTime
  have hs : ComplexityTheory.IsPolyTime (fun p : Input => state (base p)) :=
    TM2Compose.isPolyTime_comp base state hb TM2GuardAllStep.second_isPolyTime
  have hread : ComplexityTheory.IsPolyTime (fun p : Input => read (base p)) :=
    TM2Compose.isPolyTime_comp (fun p : Input => right (base p)) (fun xs : Bits => xs.headD false)
      hr Source284BitListAccessTM2.head_isPolyTime
  have hi : ComplexityTheory.IsPolyTime (fun p : Input => incrementData (state (base p))) :=
    TM2Compose.isPolyTime_comp (fun p : Input => state (base p)) incrementData hs Source284IncrementTM2.incrementData_isPolyTime
  have hii : ComplexityTheory.IsPolyTime (fun p : Input => incrementData (incrementData (state (base p)))) :=
    TM2Compose.isPolyTime_comp (fun p : Input => incrementData (state (base p))) incrementData hi Source284IncrementTM2.incrementData_isPolyTime
  have he : ComplexityTheory.IsPolyTime extraState := TM2If.if_isPolyTime _ _ _ hread hii hs
  have hhead : ComplexityTheory.IsPolyTime (fun p : Input => (choices p).headD false) :=
    TM2Compose.isPolyTime_comp choices (fun xs : Bits => xs.headD false) hch Source284BitListAccessTM2.head_isPolyTime
  have htail : ComplexityTheory.IsPolyTime (fun p : Input => (right (base p)).tail) :=
    TM2Compose.isPolyTime_comp (fun p : Input => right (base p)) (List.tail : Bits → Bits) hr Source284BitListAccessTM2.tail_isPolyTime
  have hn : ComplexityTheory.IsPolyTime newRight := by
    have hp := TM2GuardAllStep.pair_isPolyTime (fun p : Input => (choices p).headD false)
      (fun p : Input => (right (base p)).tail) hhead htail
    exact TM2Compose.isPolyTime_comp _ (TM2ListAppend.cons (α := Bool)) hp TM2ListAppend.cons_isPolyTime
  have htapes := TM2GuardAllStep.pair_isPolyTime (fun p : Input => left (base p)) newRight hl hn
  have hctx := TM2GuardAllStep.pair_isPolyTime (fun p : Input => code (base p))
    (fun p : Input => (left (base p),newRight p)) hc htapes
  have hp : ComplexityTheory.IsPolyTime prepared :=
    TM2GuardAllStep.pair_isPolyTime (fun p : Input => (code (base p),(left (base p),newRight p))) extraState hctx he
  have hstep := TM2Compose.isPolyTime_comp prepared Source284EvaluatorPackedStep.step hp Source284EvaluatorPackedStep.step_isPolyTime
  have hnch : ComplexityTheory.IsPolyTime nextChoices :=
    TM2Compose.isPolyTime_comp choices (List.tail : Bits → Bits) hch Source284BitListAccessTM2.tail_isPolyTime
  have hnext := TM2GuardAllStep.pair_isPolyTime (fun p : Input => Source284EvaluatorPackedStep.step (prepared p)) nextChoices hstep hnch
  have hz : ComplexityTheory.IsPolyTime (fun p : Input => zero (base p)) :=
    TM2Compose.isPolyTime_comp (fun p : Input => state (base p)) isZero hs Source284ZeroTM2.isZero_isPolyTime
  have hid : ComplexityTheory.IsPolyTime (id : Input → Input) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  exact TM2If.if_isPolyTime _ _ _ hz hid hnext

/-- The two source developments use the same virtual-zero unary record
stream, including noncanonical finite programs. -/
theorem readRecord_eq_popUnary (n : Nat) :
    Source284Relative.readRecord n = Source.popUnary n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Source284Relative.readRecord, Source.popUnary]
    by_cases h : n % 2 = 1
    · have hn : 0 < n := by omega
      simp only [h, ↓reduceIte, ↓reduceDIte]
      rw [ih (n/2) (by omega)]
    · simp [h]

theorem dropRecords_eq_skipUnary (program count : Nat) :
    Source284Relative.dropRecords program count = Source.skipUnary count program := by
  induction count generalizing program with
  | zero => rfl
  | succ count ih =>
    simp only [Source284Relative.dropRecords, Source.skipUnary, readRecord_eq_popUnary]
    exact ih _

theorem record_eq (program count : Nat) :
    Source284Relative.record program count = (Source.popUnary (Source.skipUnary count program)).1 := by
  simp [Source284Relative.record,dropRecords_eq_skipUnary,readRecord_eq_popUnary]

/-- The temporary state and scanned bit select exactly the source's
`state - 1 + 2 * read + choice` record. -/
theorem extraState_value (p : Input) :
    value (extraState p) = value (state (base p)) + 2*(value (right (base p)) % 2) := by
  have h := value_head (right (base p))
  cases hb : (right (base p)).headD false with
  | false =>
    rw [hb] at h
    have hv : value (right (base p)) % 2 = 0 := by simpa only [bitValue,Bool.false_eq_true,if_false] using h.symm
    unfold extraState Source284EvaluatorPackedStep.read
    rw [hb]
    simp only [Bool.false_eq_true,if_false,hv,Nat.mul_zero,Nat.add_zero]
  | true =>
    rw [hb] at h
    have hv : value (right (base p)) % 2 = 1 := by simpa only [bitValue,if_true] using h.symm
    unfold extraState Source284EvaluatorPackedStep.read
    rw [hb]
    simp only [if_true,hv,Nat.mul_one,increment_value]

theorem newRight_value (p : Input) :
    value (newRight p) = 2*(value (right (base p))/2) + value (choices p)%2 := by
  have h := value_head (choices p)
  rw [← value_tail]
  simp only [newRight, value]
  simpa [bitValue] using congrArg (fun n => 2 * value (right (base p)).tail + n) h

/-- Full numeric two-half-tape interpretation of a packed step. -/
def numericConfig (p : Input) : Source284Relative.Config := denote (config (base p))

/-- The 285 reference transition, with choice bits supplied as a natural.
State zero is absorbing, including after the final HALT write and move. -/
def numericStep (program : Nat) (c : Source284Relative.Config) (choice : Nat) :
    Source284Relative.Config :=
  if c.state = 0 then c else
    let row := (Source.popUnary (Source.skipUnary (c.state-1+2*(c.right%2)+choice%2) program)).1
    if (row/2)%2 = 1 then ⟨2*(c.right/2)+row%2,c.left,row/4⟩
    else ⟨2*c.left+row%2,c.right/2,row/4⟩

theorem step_config (p : Input) :
    numericConfig (step p) = numericStep (value (code (base p))) (numericConfig p) (value (choices p)) := by
  by_cases hz : zero (base p) = true
  · have hstate : value (state (base p)) = 0 := (isZero_correct _).1 hz
    simp [step,hz,numericStep,numericConfig,config,denote,hstate]
  · have hstate : value (state (base p)) ≠ 0 := by
      intro h
      exact hz ((isZero_correct _).2 h)
    have hden := denote_step (prepared p)
    have he := extraState_value p
    have hr := newRight_value p
    have hc : value (choices p)%2 < 2 := Nat.mod_lt _ (by decide)
    have hread : value (newRight p)%2 = value (choices p)%2 := by omega
    have hforward : value (newRight p)/2 = value (right (base p))/2 := by omega
    have hpos : value (extraState p) ≠ 0 := by omega
    unfold numericConfig
    rw [step,if_neg hz]
    change denote (config (Source284EvaluatorPackedStep.step (prepared p))) = _
    rw [hden]
    change Source284Relative.step (value (code (base p)))
      ⟨value (left (base p)),value (newRight p),value (extraState p)⟩ =
      numericStep (value (code (base p)))
        ⟨value (left (base p)),value (right (base p)),value (state (base p))⟩ (value (choices p))
    simp only [Source284Relative.step,numericStep,hpos,hstate,if_false]
    rw [he,hread,hforward,record_eq]
    have hor : value (state (base p)) + 2*(value (right (base p))%2) - 1 =
        value (state (base p))-1+2*(value (right (base p))%2) := by omega
    rw [hor]

def toSim (c : Source284Relative.Config) (choice : Nat) : Source.SimState :=
  ⟨c.left,c.right/2,c.state-1+2*(c.right%2),choice⟩

/-- The full numeric step agrees with the selected source transition,
including consumption of exactly one choice bit. -/
theorem numericStep_matches (program : Nat) (c : Source284Relative.Config) (choice : Nat)
    (hc : c.state ≠ 0) :
    Source.simStep program (toSim c choice) =
      if (numericStep program c choice).state = 0 then none
      else some (toSim (numericStep program c choice) (choice/2)) := by
  have hs : (toSim c choice).selector = c.state-1+2*bitVal (c.right.testBit 0) := by
    simp only [toSim]
    rw [bitVal_lowBit]
  have ha := action_matches_row program c.state (toSim c choice) (c.right.testBit 0) hs
  change action program (toSim c choice) = rowAction program c.state (c.right.testBit 0) (choice.testBit 0) at ha
  rw [CandidateNumericStep.simStep_as_action,ha]
  unfold numericStep
  rw [if_neg hc]
  unfold rowAction
  have hb (x : Nat) : (if x%2=1 then 1 else 0) = x%2 := by
    simpa [bitVal] using bitVal_decide_one (x%2) (Nat.mod_lt _ (by decide))
  simp only [Nat.testBit_zero,bitVal_decide_one _ (Nat.mod_lt _ (by decide))]
  generalize he : (Source.popUnary (Source.skipUnary
    (c.state-1+2*(c.right%2)+choice%2) program)).1 = row
  by_cases ht : (row/2)%2 = 1 <;> by_cases hn : row/4 = 0 <;>
    simp [ht,hn,toSim,behindNumber,aheadNumber,nextRead,bitVal,Nat.testBit_zero,hb]

theorem choice_step (p : Input) (h : zero (base p) ≠ true) :
    value (choices (step p)) = value (choices p) / 2 := by
  rw [step,if_neg h]
  exact value_tail _

theorem code_step (p : Input) : code (base (step p)) = code (base p) := by
  unfold step
  split_ifs
  · rfl
  · change code (Source284EvaluatorPackedStep.step (prepared p)) = code (base p)
    rw [code_unchanged]
    rfl

theorem zero_step (p : Input) (h : (numericConfig p).state = 0) : step p = p := by
  have hz : zero (base p) = true := (isZero_correct _).2 h
  simp [step,hz]

theorem run_zero_state (p : Input) (h : (numericConfig p).state = 0) (clock : Nat) :
    TM2UnaryIterate.run step p clock = p := by
  induction clock with
  | zero => rfl
  | succ n ih => simpa [TM2UnaryIterate.run,zero_step p h] using ih

/-- Every finite bit-list run agrees with the original source HALT test at
exactly the supplied clock, for arbitrary program, tape and choice bits. -/
theorem run_matches (p : Input) (clock : Nat) (h : (numericConfig p).state ≠ 0) :
    Source.haltedWithin (value (code (base p))) clock (toSim (numericConfig p) (value (choices p))) = true ↔
      (numericConfig (TM2UnaryIterate.run step p clock)).state = 0 := by
  induction clock generalizing p with
  | zero => simp [Source.haltedWithin,TM2UnaryIterate.run,h]
  | succ n ih =>
    have hz : zero (base p) ≠ true := by
      intro hz
      exact h ((isZero_correct _).1 hz)
    have hs := numericStep_matches (value (code (base p))) (numericConfig p) (value (choices p)) h
    rw [← step_config] at hs
    rw [← choice_step p hz] at hs
    change (Source.simStep (value (code (base p))) (toSim (numericConfig p) (value (choices p)))) = _ at hs
    change Source.haltedWithin _ (n+1) _ = true ↔
      (numericConfig (TM2UnaryIterate.run step (step p) n)).state = 0
    by_cases hn : (numericConfig (step p)).state = 0
    · simp [hn] at hs
      rw [run_zero_state (step p) hn n]
      simp [Source.haltedWithin,hs,hn]
    · simp [hn] at hs
      rw [Source.haltedWithin,hs]
      simpa only [code_step] using ih (step p) hn

end Shared.PNP.Record285.ReferenceChoiceStep
