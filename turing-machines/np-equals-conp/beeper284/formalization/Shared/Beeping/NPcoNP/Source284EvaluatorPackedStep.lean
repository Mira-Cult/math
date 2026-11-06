import Shared.Beeping.NPcoNP.Source284OrdinalTM2
import Shared.Beeping.NPcoNP.Source284BitListAccessTM2
import Shared.ComplexityBridge.TM2Serialize

/-! A canonical tuple encoding of one 284 bounded-evaluator step. The code
field is carried unchanged, and all execution data are Boolean lists. This
module proves the full single step polynomial time, not an iterated evaluator
or complexity-class inclusion. -/
namespace Shared.Beeping.NPcoNP.Source284EvaluatorPackedStep

open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284RecordBitCost
open Shared.Beeping.NPcoNP.Source284EvaluatorBitStep
open Shared.Codes.BitNumeralCompare (value)

abbrev Bits := List Bool
abbrev Context := Bits × (Bits × Bits)  -- code, (left, right)
abbrev Packed := Context × Bits         -- context, state

def code (p : Packed) : Bits := p.1.1
def tapes (p : Packed) : Bits × Bits := p.1.2
def left (p : Packed) : Bits := p.1.2.1
def right (p : Packed) : Bits := p.1.2.2
def state (p : Packed) : Bits := p.2
def read (p : Packed) : Bool := (right p).headD false
def index (p : Packed) : Bits := ordinal (state p) (read p)
def row (p : Packed) : Nat := Source284RecordTM2.lookup (code p,index p)
def rowBits (p : Packed) : Bits := (row p).bits
def written (p : Packed) : Bool := (rowBits p).headD false
def turn (p : Packed) : Bool := (rowBits p).tail.headD false
def next (p : Packed) : Bits := (rowBits p).tail.tail
def forward (p : Packed) : Bits := (right p).tail
def zero (p : Packed) : Bool := isZero (state p)
def turnResult (p : Packed) : Packed := ((code p,(written p :: forward p,left p)),next p)
def forwardResult (p : Packed) : Packed := ((code p,(written p :: left p,forward p)),next p)

def step (p : Packed) : Packed :=
  if zero p then p else if turn p then turnResult p else forwardResult p

def config (p : Packed) : Source284EvaluatorBitStep.Config := ⟨left p,right p,state p⟩

theorem code_unchanged (p : Packed) : code (step p) = code p := by
  unfold step
  split_ifs <;> rfl

/-- The tuple representation denotes exactly the executable bit-list step. -/
theorem config_step (p : Packed) :
    config (step p) = Source284EvaluatorBitStep.step (code p) (config p) := by
  rcases p with ⟨⟨program,⟨l,r⟩⟩,s⟩
  by_cases hz : isZero s = true
  · simp [step, zero, state, config, code, left, right, Source284EvaluatorBitStep.step, hz]
  · by_cases ht : (Source284RecordTM2.lookup (program,ordinal s (r.headD false))).bits.tail.headD false = true <;>
      simp [step, zero, state, config, code, left, right, Source284EvaluatorBitStep.step,
        turn, rowBits, row, index, read, written, next, forward, turnResult, forwardResult, hz, ht] <;>
      split_ifs <;> rfl

theorem denote_step (p : Packed) :
    denote (config (step p)) = Source284Relative.step (value (code p)) (denote (config p)) := by
  rw [config_step]
  exact Source284EvaluatorBitStep.step_correct _ _

/-- Every component is an independently verified canonical polynomial-time
function; conditionals charge both branches and output serialization. -/
theorem step_isPolyTime : ComplexityTheory.IsPolyTime step := by
  let context : Packed → Context := fun p => p.1
  have hctx : ComplexityTheory.IsPolyTime context := TM2PairFirst.first_isPolyTime
  have hs : ComplexityTheory.IsPolyTime state := TM2GuardAllStep.second_isPolyTime
  have hc : ComplexityTheory.IsPolyTime code :=
    TM2Compose.isPolyTime_comp context (fun p : Context => p.1) hctx TM2PairFirst.first_isPolyTime
  have htapes : ComplexityTheory.IsPolyTime tapes :=
    TM2Compose.isPolyTime_comp context (fun p : Context => p.2) hctx TM2GuardAllStep.second_isPolyTime
  have hl : ComplexityTheory.IsPolyTime left :=
    TM2Compose.isPolyTime_comp tapes (fun p : Bits × Bits => p.1) htapes TM2PairFirst.first_isPolyTime
  have hr : ComplexityTheory.IsPolyTime right :=
    TM2Compose.isPolyTime_comp tapes (fun p : Bits × Bits => p.2) htapes TM2GuardAllStep.second_isPolyTime
  have hread : ComplexityTheory.IsPolyTime read :=
    TM2Compose.isPolyTime_comp right (fun xs : Bits => xs.headD false) hr Source284BitListAccessTM2.head_isPolyTime
  have hordargs := TM2GuardAllStep.pair_isPolyTime state read hs hread
  have hi : ComplexityTheory.IsPolyTime index :=
    TM2Compose.isPolyTime_comp (fun p : Packed => (state p,read p))
      (fun p : Bits × Bool => ordinal p.1 p.2) hordargs Source284OrdinalTM2.ordinal_isPolyTime
  have hrowargs := TM2GuardAllStep.pair_isPolyTime code index hc hi
  have hrow : ComplexityTheory.IsPolyTime row :=
    TM2Compose.isPolyTime_comp (fun p : Packed => (code p,index p))
      Source284RecordTM2.lookup hrowargs Source284RecordTM2.lookup_isPolyTime
  have hbits : ComplexityTheory.IsPolyTime (fun n : Nat => n.bits) := by
    have h := TM2Serialize.isPolyTime (α := Nat)
    change ComplexityTheory.IsPolyTime (fun n : Nat => Computability.encodeNat n) at h
    simpa only [CNFEncodingComputability.encodeNat_bits] using h
  have hrowbits : ComplexityTheory.IsPolyTime rowBits :=
    TM2Compose.isPolyTime_comp row (fun n : Nat => n.bits) hrow hbits
  have hw : ComplexityTheory.IsPolyTime written :=
    TM2Compose.isPolyTime_comp rowBits (fun xs : Bits => xs.headD false) hrowbits Source284BitListAccessTM2.head_isPolyTime
  have htailrow : ComplexityTheory.IsPolyTime (fun p : Packed => (rowBits p).tail) :=
    TM2Compose.isPolyTime_comp rowBits (List.tail : Bits → Bits) hrowbits Source284BitListAccessTM2.tail_isPolyTime
  have ht : ComplexityTheory.IsPolyTime turn :=
    TM2Compose.isPolyTime_comp (fun p : Packed => (rowBits p).tail)
      (fun xs : Bits => xs.headD false) htailrow Source284BitListAccessTM2.head_isPolyTime
  have hn : ComplexityTheory.IsPolyTime next :=
    TM2Compose.isPolyTime_comp (fun p : Packed => (rowBits p).tail)
      (List.tail : Bits → Bits) htailrow Source284BitListAccessTM2.tail_isPolyTime
  have hfor : ComplexityTheory.IsPolyTime forward :=
    TM2Compose.isPolyTime_comp right (List.tail : Bits → Bits) hr Source284BitListAccessTM2.tail_isPolyTime
  have hz : ComplexityTheory.IsPolyTime zero :=
    TM2Compose.isPolyTime_comp state isZero hs Source284ZeroTM2.isZero_isPolyTime
  have hconsForward : ComplexityTheory.IsPolyTime (fun p : Packed => written p :: forward p) := by
    have hp := TM2GuardAllStep.pair_isPolyTime written forward hw hfor
    have h := TM2Compose.isPolyTime_comp (fun p : Packed => (written p,forward p))
      (TM2ListAppend.cons (α := Bool)) hp TM2ListAppend.cons_isPolyTime
    simpa [TM2ListAppend.cons] using h
  have hconsLeft : ComplexityTheory.IsPolyTime (fun p : Packed => written p :: left p) := by
    have hp := TM2GuardAllStep.pair_isPolyTime written left hw hl
    have h := TM2Compose.isPolyTime_comp (fun p : Packed => (written p,left p))
      (TM2ListAppend.cons (α := Bool)) hp TM2ListAppend.cons_isPolyTime
    simpa [TM2ListAppend.cons] using h
  have hturnTapes := TM2GuardAllStep.pair_isPolyTime (fun p : Packed => written p :: forward p) left hconsForward hl
  have hfwdTapes := TM2GuardAllStep.pair_isPolyTime (fun p : Packed => written p :: left p) forward hconsLeft hfor
  have hturnContext := TM2GuardAllStep.pair_isPolyTime code (fun p : Packed => (written p :: forward p,left p)) hc hturnTapes
  have hfwdContext := TM2GuardAllStep.pair_isPolyTime code (fun p : Packed => (written p :: left p,forward p)) hc hfwdTapes
  have hturnResult : ComplexityTheory.IsPolyTime turnResult :=
    TM2GuardAllStep.pair_isPolyTime (fun p : Packed => (code p,(written p :: forward p,left p))) next hturnContext hn
  have hfwdResult : ComplexityTheory.IsPolyTime forwardResult :=
    TM2GuardAllStep.pair_isPolyTime (fun p : Packed => (code p,(written p :: left p,forward p))) next hfwdContext hn
  have hactive := TM2If.if_isPolyTime turn turnResult forwardResult ht hturnResult hfwdResult
  have hid : ComplexityTheory.IsPolyTime (id : Packed → Packed) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have h := TM2If.if_isPolyTime zero id (fun p => if turn p then turnResult p else forwardResult p) hz hid hactive
  exact h

end Shared.Beeping.NPcoNP.Source284EvaluatorPackedStep
