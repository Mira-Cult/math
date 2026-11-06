import Shared.ComplexityBridge.TM2If
import Shared.ComplexityBridge.TM2Constant
import Shared.ComplexityBridge.TM2ListAppend
import Shared.ComplexityBridge.TM2PolynomialFold

/-! A data-only bitwise fold step for the 284 marker/payload parser.
The first flag records termination and the second awaits a payload bit.
The accumulator stores parsed payload bits in reverse order.  A pending
payload at end of input needs a separate virtual-zero finalization. -/

set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284ParseFoldStep

open Shared.ComplexityBridge

abbrev Packed := (Bool × Bool) × List Bool
abbrev Input := Packed × Bool

def state (p : Input) : Packed := p.1
def flags (p : Input) : Bool × Bool := p.1.1
def done (p : Input) : Bool := p.1.1.1
def pending (p : Input) : Bool := p.1.1.2
def acc (p : Input) : List Bool := p.1.2
def bit (p : Input) : Bool := p.2

def consume (p : Input) : Packed := ((false,false), bit p :: acc p)
def mark (p : Input) : Packed := ((false,true), acc p)
def stop (p : Input) : Packed := ((true,false), acc p)

/-- Once stopped, later bits have no effect. A pending marker consumes
exactly one payload; an isolated final marker is handled by the caller. -/
def step (p : Input) : Packed :=
  if done p then state p
  else if pending p then consume p
  else if bit p then mark p else stop p

theorem step_isPolyTime : ComplexityTheory.IsPolyTime step := by
  have hs : ComplexityTheory.IsPolyTime state := TM2PairFirst.first_isPolyTime
  have hb : ComplexityTheory.IsPolyTime bit := TM2GuardAllStep.second_isPolyTime
  have hf : ComplexityTheory.IsPolyTime flags :=
    TM2Compose.isPolyTime_comp state (fun s : Packed => s.1) hs TM2PairFirst.first_isPolyTime
  have hd : ComplexityTheory.IsPolyTime done :=
    TM2Compose.isPolyTime_comp flags (fun p : Bool × Bool => p.1) hf TM2PairFirst.first_isPolyTime
  have hp : ComplexityTheory.IsPolyTime pending :=
    TM2Compose.isPolyTime_comp flags (fun p : Bool × Bool => p.2) hf TM2GuardAllStep.second_isPolyTime
  have ha : ComplexityTheory.IsPolyTime acc :=
    TM2Compose.isPolyTime_comp state (fun s : Packed => s.2) hs TM2GuardAllStep.second_isPolyTime
  have ht : ComplexityTheory.IsPolyTime (fun _ : Input => true) := TM2Constant.isPolyTime true
  have hfalse : ComplexityTheory.IsPolyTime (fun _ : Input => false) := TM2Constant.isPolyTime false
  have hff : ComplexityTheory.IsPolyTime (fun _ : Input => (false,false)) :=
    TM2GuardAllStep.pair_isPolyTime (fun _ : Input => false) (fun _ : Input => false) hfalse hfalse
  have hft : ComplexityTheory.IsPolyTime (fun _ : Input => (false,true)) :=
    TM2GuardAllStep.pair_isPolyTime (fun _ : Input => false) (fun _ : Input => true) hfalse ht
  have htf : ComplexityTheory.IsPolyTime (fun _ : Input => (true,false)) :=
    TM2GuardAllStep.pair_isPolyTime (fun _ : Input => true) (fun _ : Input => false) ht hfalse
  have hc : ComplexityTheory.IsPolyTime (fun p : Input => bit p :: acc p) := by
    have hpair := TM2GuardAllStep.pair_isPolyTime bit acc hb ha
    have h := TM2Compose.isPolyTime_comp (fun p : Input => (bit p,acc p))
      (TM2ListAppend.cons (α := Bool)) hpair TM2ListAppend.cons_isPolyTime
    simpa [TM2ListAppend.cons] using h
  have hconsume : ComplexityTheory.IsPolyTime consume :=
    TM2GuardAllStep.pair_isPolyTime (fun _ : Input => (false,false))
      (fun p : Input => bit p :: acc p) hff hc
  have hmark : ComplexityTheory.IsPolyTime mark :=
    TM2GuardAllStep.pair_isPolyTime (fun _ : Input => (false,true)) acc hft ha
  have hstop : ComplexityTheory.IsPolyTime stop :=
    TM2GuardAllStep.pair_isPolyTime (fun _ : Input => (true,false)) acc htf ha
  have hmarker := TM2If.if_isPolyTime bit mark stop hb hmark hstop
  have hwork := TM2If.if_isPolyTime pending consume
    (fun p => if bit p then mark p else stop p) hp hconsume hmarker
  exact TM2If.if_isPolyTime done state
    (fun p => if pending p then consume p else if bit p then mark p else stop p)
    hd hs hwork

end Shared.Beeping.NPcoNP.Source284ParseFoldStep
