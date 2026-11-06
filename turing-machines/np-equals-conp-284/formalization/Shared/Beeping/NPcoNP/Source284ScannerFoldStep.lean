import Shared.Beeping.NPcoNP.Source284DecrementTM2
import Shared.Beeping.NPcoNP.Source284ZeroTM2
import Shared.ComplexityBridge.TM2If
import Shared.ComplexityBridge.TM2Constant
import Shared.ComplexityBridge.TM2PolynomialFold

/-! A data-only finite-state fold step for the 284 unary-record bit scanner.
It uses the separately proved canonical TM2 zero-test and decrement. This
file establishes a polynomial-time *single step*, not yet the whole scanner. -/

set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284ScannerFoldStep

open Shared.Beeping.NPcoNP.Source284RecordBitCost
open Shared.ComplexityBridge

/-- `done`, current binary index, and reversed unary result. -/
abbrev State := Bool × (List Bool × List Bool)
abbrev Input := State × Bool

def state (p : Input) : State := p.1
def done (p : Input) : Bool := p.1.1
def fields (p : Input) : List Bool × List Bool := p.1.2
def index (p : Input) : List Bool := p.1.2.1
def acc (p : Input) : List Bool := p.1.2.2
def bit (p : Input) : Bool := p.2
def zero (p : Input) : Bool := isZero (index p)
def grow (p : Input) : State := (false,(index p,true :: acc p))
def stop (p : Input) : State := (true, fields p)
def descend (p : Input) : State := (false,(decBits (index p),acc p))

/-- Every branch is total; after the first delimiter of the requested record
the accumulator is retained without further decoding. -/
def step (p : Input) : State :=
  if done p then state p
  else if zero p then (if bit p then grow p else stop p)
  else if bit p then state p else descend p

theorem step_isPolyTime : ComplexityTheory.IsPolyTime step := by
  have hs : ComplexityTheory.IsPolyTime state := TM2PairFirst.first_isPolyTime
  have hb : ComplexityTheory.IsPolyTime bit := TM2GuardAllStep.second_isPolyTime
  have hd : ComplexityTheory.IsPolyTime done :=
    TM2Compose.isPolyTime_comp state (fun s : State => s.1) hs TM2PairFirst.first_isPolyTime
  have hf : ComplexityTheory.IsPolyTime fields :=
    TM2Compose.isPolyTime_comp state (fun s : State => s.2) hs TM2GuardAllStep.second_isPolyTime
  have hi : ComplexityTheory.IsPolyTime index :=
    TM2Compose.isPolyTime_comp fields (fun p : List Bool × List Bool => p.1) hf TM2PairFirst.first_isPolyTime
  have ha : ComplexityTheory.IsPolyTime acc :=
    TM2Compose.isPolyTime_comp fields (fun p : List Bool × List Bool => p.2) hf TM2GuardAllStep.second_isPolyTime
  have hz : ComplexityTheory.IsPolyTime zero :=
    TM2Compose.isPolyTime_comp index isZero hi Source284ZeroTM2.isZero_isPolyTime
  have hdec : ComplexityTheory.IsPolyTime (fun p : Input => decBits (index p)) :=
    TM2Compose.isPolyTime_comp index decBits hi Source284DecrementTM2.decBits_isPolyTime
  have htrue : ComplexityTheory.IsPolyTime (fun _ : Input => true) := TM2Constant.isPolyTime true
  have hfalse : ComplexityTheory.IsPolyTime (fun _ : Input => false) := TM2Constant.isPolyTime false
  have hcons : ComplexityTheory.IsPolyTime (fun p : Input => true :: acc p) := by
    have hp := TM2GuardAllStep.pair_isPolyTime (fun _ : Input => true) acc htrue ha
    have h := TM2Compose.isPolyTime_comp (fun p : Input => (true,acc p))
      (TM2ListAppend.cons (α := Bool)) hp TM2ListAppend.cons_isPolyTime
    simpa [TM2ListAppend.cons] using h
  have hgfields : ComplexityTheory.IsPolyTime (fun p : Input => (index p,true :: acc p)) :=
    TM2GuardAllStep.pair_isPolyTime index (fun p => true :: acc p) hi hcons
  have hg : ComplexityTheory.IsPolyTime grow :=
    TM2GuardAllStep.pair_isPolyTime (fun _ : Input => false) (fun p => (index p,true :: acc p)) hfalse hgfields
  have ht : ComplexityTheory.IsPolyTime stop :=
    TM2GuardAllStep.pair_isPolyTime (fun _ : Input => true) fields htrue hf
  have hhfields : ComplexityTheory.IsPolyTime (fun p : Input => (decBits (index p),acc p)) :=
    TM2GuardAllStep.pair_isPolyTime (fun p => decBits (index p)) acc hdec ha
  have hh : ComplexityTheory.IsPolyTime descend :=
    TM2GuardAllStep.pair_isPolyTime (fun _ : Input => false) (fun p => (decBits (index p),acc p)) hfalse hhfields
  have hzero := TM2If.if_isPolyTime bit grow stop hb hg ht
  have hnonzero := TM2If.if_isPolyTime bit state descend hb hs hh
  have hwork := TM2If.if_isPolyTime zero (fun p => if bit p then grow p else stop p)
    (fun p => if bit p then state p else descend p) hz hzero hnonzero
  exact TM2If.if_isPolyTime done state
    (fun p => if zero p then (if bit p then grow p else stop p)
      else if bit p then state p else descend p) hd hs hwork

/-- The remaining contribution of a fold state to the final scanner output. -/
def observation (s : State) (remaining : List Bool) : List Bool :=
  s.2.2.reverse ++ if s.1 then [] else scan remaining s.2.1

/-- One fold step consumes exactly one source bit without changing the final
observed result. This holds for arbitrary, even noncanonical, indices. -/
theorem observation_step (s : State) (b : Bool) (remaining : List Bool) :
    observation (step (s,b)) remaining = observation s (b :: remaining) := by
  rcases s with ⟨d,idx,as⟩
  cases d <;> cases b <;> cases hz : isZero idx <;>
    simp [observation, step, state, done, fields, index, acc, bit, zero,
      grow, stop, descend, scan, hz, List.reverse_cons, List.append_assoc]

theorem observation_fold (s : State) (code : List Bool) :
    observation (TM2PolynomialFold.fold step s code) [] = observation s code := by
  induction code generalizing s with
  | nil => rfl
  | cons b bs ih =>
    change observation (TM2PolynomialFold.fold step (step (s,b)) bs) [] = _
    rw [ih, observation_step]

/-- The fold computes exactly the existing executable scanner. -/
theorem fold_correct (code indexBits : List Bool) :
    (TM2PolynomialFold.fold step (false,(indexBits,[])) code).2.2.reverse =
      scan code indexBits := by
  have h := observation_fold (false,(indexBits,[])) code
  simpa [observation, scan] using h

end Shared.Beeping.NPcoNP.Source284ScannerFoldStep
