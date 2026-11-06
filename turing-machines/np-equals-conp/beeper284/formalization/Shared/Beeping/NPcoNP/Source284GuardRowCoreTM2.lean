import Shared.Beeping.NPcoNP.Source284BoundedPairTM2
import Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2
import Shared.ComplexityBridge.TM2CircuitOutputWorker
import Shared.ComplexityBridge.TM2FixedRows

/-! Canonical polynomial-time arithmetic worker for a countdown-guard row.
Both bounds are supplied as unary lists; pairing clamps over-budget values.
The worker is total on every encoded input and does not construct a table. -/
namespace Shared.Beeping.NPcoNP.Source284GuardRowCoreTM2

open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284BoundedPairTM2
open Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2

abbrev Bounds := List Bool × List Bool
abbrev Input := List Bool × (List Bool × (Nat × EncRow))

def isEmpty (xs : List Bool) : Bool := xs.isEmpty

theorem isEmpty_isPolyTime : ComplexityTheory.IsPolyTime isEmpty := by
  have h := TM2Compose.isPolyTime_comp TM2CircuitOutputWorker.nonempty (fun b => !b)
    TM2CircuitOutputWorker.nonempty_isPolyTime TM2GateDispatch.not_isPolyTime
  have he : (fun xs : List Bool => !TM2CircuitOutputWorker.nonempty xs) = isEmpty := by
    funext xs
    cases xs <;> simp [isEmpty, TM2CircuitOutputWorker.nonempty, TM2BoundedWitnessGuard.numericNe]
  rw [he] at h
  exact h

/-- Sink index: zero at a zero cutoff, otherwise the bounded pair of the
cutoff and original-state lengths. -/
def sink (p : Bounds) : Nat :=
  if p.1.isEmpty then 0 else pairBounded (p.1 ++ p.2,(p.1.length,p.2.length))

theorem sink_isPolyTime : ComplexityTheory.IsPolyTime sink := by
  let cutoff : Bounds → List Bool := fun p => p.1
  let states : Bounds → List Bool := fun p => p.2
  let budget : Bounds → List Bool := fun p => p.1 ++ p.2
  let tc : Bounds → Nat := fun p => p.1.length
  let nc : Bounds → Nat := fun p => p.2.length
  let flag : Bounds → Bool := fun p => (cutoff p).isEmpty
  let zero : Bounds → Nat := fun _ => 0
  let pair : Bounds → Nat := fun p => pairBounded (budget p,(tc p,nc p))
  have ht : ComplexityTheory.IsPolyTime cutoff := TM2PairFirst.first_isPolyTime
  have hn : ComplexityTheory.IsPolyTime states := TM2GuardAllStep.second_isPolyTime
  have hb : ComplexityTheory.IsPolyTime budget := TM2ListAppend.append_isPolyTime
  have htc : ComplexityTheory.IsPolyTime tc := TM2Compose.isPolyTime_comp cutoff List.length ht TM2BinaryListLength.length_isPolyTime
  have hnc : ComplexityTheory.IsPolyTime nc := TM2Compose.isPolyTime_comp states List.length hn TM2BinaryListLength.length_isPolyTime
  have hf : ComplexityTheory.IsPolyTime flag := TM2Compose.isPolyTime_comp cutoff isEmpty ht isEmpty_isPolyTime
  have hz : ComplexityTheory.IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have hp : ComplexityTheory.IsPolyTime pair :=
    TM2Compose.isPolyTime_comp (fun p => (budget p,(tc p,nc p))) pairBounded
      (TM2GuardAllStep.pair_isPolyTime budget (fun p => (tc p,nc p)) hb
        (TM2GuardAllStep.pair_isPolyTime tc nc htc hnc)) pairBounded_isPolyTime
  exact TM2If.if_isPolyTime flag zero pair hf hz hp

def cutoff (p : Input) : List Bool := p.1
def states (p : Input) : List Bool := p.2.1
def elapsed (p : Input) : Nat := p.2.2.1
def original (p : Input) : EncRow := p.2.2.2

def budget (p : Input) : List Bool := cutoff p ++ states p

def nextElapsed (p : Input) : Nat := elapsed p + 1

def writeBit (p : Input) : Bool := (original p).1
def turnBit (p : Input) : Bool := (original p).2.1
def continues (p : Input) : Bool := (original p).2.2.1
def oldDest (p : Input) : Nat := (original p).2.2.2

def active (p : Input) : Bool :=
  TM2BoundedWitnessGuard.guard (cutoff p,nextElapsed p) &&
    TM2BoundedWitnessGuard.guard (states p,oldDest p)

def target (p : Input) : Nat :=
  if active p then pairBounded (budget p,(nextElapsed p,oldDest p))
  else sink (cutoff p,states p)

def destination (p : Input) : Nat := if continues p then target p else 0

def core (p : Input) : EncRow := (writeBit p,turnBit p,continues p,destination p)

private theorem cutoff_poly : ComplexityTheory.IsPolyTime cutoff := TM2PairFirst.first_isPolyTime
private theorem rest_poly : ComplexityTheory.IsPolyTime (fun p : Input => p.2) := TM2GuardAllStep.second_isPolyTime
private theorem states_poly : ComplexityTheory.IsPolyTime states :=
  TM2Compose.isPolyTime_comp (fun p : Input => p.2) (fun p : List Bool × (Nat × EncRow) => p.1)
    rest_poly TM2PairFirst.first_isPolyTime
private theorem rest2_poly : ComplexityTheory.IsPolyTime (fun p : Input => p.2.2) :=
  TM2Compose.isPolyTime_comp (fun p : Input => p.2) (fun p : List Bool × (Nat × EncRow) => p.2)
    rest_poly TM2GuardAllStep.second_isPolyTime
private theorem elapsed_poly : ComplexityTheory.IsPolyTime elapsed :=
  TM2Compose.isPolyTime_comp (fun p : Input => p.2.2) (fun p : Nat × EncRow => p.1)
    rest2_poly TM2PairFirst.first_isPolyTime
private theorem original_poly : ComplexityTheory.IsPolyTime original :=
  TM2Compose.isPolyTime_comp (fun p : Input => p.2.2) (fun p : Nat × EncRow => p.2)
    rest2_poly TM2GuardAllStep.second_isPolyTime
private theorem rowtail_poly : ComplexityTheory.IsPolyTime (fun p : Input => (original p).2) :=
  TM2Compose.isPolyTime_comp original (fun r : EncRow => r.2) original_poly TM2GuardAllStep.second_isPolyTime
private theorem rowlast_poly : ComplexityTheory.IsPolyTime (fun p : Input => (original p).2.2) :=
  TM2Compose.isPolyTime_comp (fun p : Input => (original p).2) (fun x : Bool × Bool × Nat => x.2)
    rowtail_poly TM2GuardAllStep.second_isPolyTime
private theorem write_poly : ComplexityTheory.IsPolyTime writeBit :=
  TM2Compose.isPolyTime_comp original (fun r : EncRow => r.1) original_poly TM2PairFirst.first_isPolyTime
private theorem turn_poly : ComplexityTheory.IsPolyTime turnBit :=
  TM2Compose.isPolyTime_comp (fun p : Input => (original p).2) (fun x : Bool × Bool × Nat => x.1)
    rowtail_poly TM2PairFirst.first_isPolyTime
private theorem continues_poly : ComplexityTheory.IsPolyTime continues :=
  TM2Compose.isPolyTime_comp (fun p : Input => (original p).2.2) (fun x : Bool × Nat => x.1)
    rowlast_poly TM2PairFirst.first_isPolyTime
private theorem oldDest_poly : ComplexityTheory.IsPolyTime oldDest :=
  TM2Compose.isPolyTime_comp (fun p : Input => (original p).2.2) (fun x : Bool × Nat => x.2)
    rowlast_poly TM2GuardAllStep.second_isPolyTime
private theorem next_poly : ComplexityTheory.IsPolyTime nextElapsed :=
  TM2Compose.isPolyTime_comp elapsed (fun n => n+1) elapsed_poly (TM2FixedRows.addFixed_isPolyTime 1)
private theorem budget_poly : ComplexityTheory.IsPolyTime budget :=
  TM2CircuitTemplate.append_isPolyTime cutoff states cutoff_poly states_poly

theorem active_isPolyTime : ComplexityTheory.IsPolyTime active := by
  let a : Input → Bool := fun p => TM2BoundedWitnessGuard.guard (cutoff p,nextElapsed p)
  let b : Input → Bool := fun p => TM2BoundedWitnessGuard.guard (states p,oldDest p)
  have ha : ComplexityTheory.IsPolyTime a := TM2Compose.isPolyTime_comp
    (fun p => (cutoff p,nextElapsed p)) TM2BoundedWitnessGuard.guard
    (TM2GuardAllStep.pair_isPolyTime cutoff nextElapsed cutoff_poly next_poly) TM2BoundedWitnessGuard.guard_isPolyTime
  have hb : ComplexityTheory.IsPolyTime b := TM2Compose.isPolyTime_comp
    (fun p => (states p,oldDest p)) TM2BoundedWitnessGuard.guard
    (TM2GuardAllStep.pair_isPolyTime states oldDest states_poly oldDest_poly) TM2BoundedWitnessGuard.guard_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p => (a p,b p)) (fun z : Bool × Bool => z.1 && z.2)
    (TM2GuardAllStep.pair_isPolyTime a b ha hb) TM2GateDispatch.and_isPolyTime

theorem target_isPolyTime : ComplexityTheory.IsPolyTime target := by
  let yes : Input → Nat := fun p => pairBounded (budget p,(nextElapsed p,oldDest p))
  let no : Input → Nat := fun p => sink (cutoff p,states p)
  have hy : ComplexityTheory.IsPolyTime yes := TM2Compose.isPolyTime_comp
    (fun p => (budget p,(nextElapsed p,oldDest p))) pairBounded
    (TM2GuardAllStep.pair_isPolyTime budget (fun p => (nextElapsed p,oldDest p)) budget_poly
      (TM2GuardAllStep.pair_isPolyTime nextElapsed oldDest next_poly oldDest_poly)) pairBounded_isPolyTime
  have hn : ComplexityTheory.IsPolyTime no := TM2Compose.isPolyTime_comp (fun p => (cutoff p,states p)) sink
    (TM2GuardAllStep.pair_isPolyTime cutoff states cutoff_poly states_poly) sink_isPolyTime
  exact TM2If.if_isPolyTime active yes no active_isPolyTime hy hn

theorem destination_isPolyTime : ComplexityTheory.IsPolyTime destination := by
  exact TM2If.if_isPolyTime continues target (fun _ : Input => 0) continues_poly target_isPolyTime
    TM2EmptyConstant.zero_isPolyTime

theorem core_isPolyTime : ComplexityTheory.IsPolyTime core :=
  row_isPolyTime writeBit turnBit continues destination write_poly turn_poly continues_poly destination_isPolyTime

end Shared.Beeping.NPcoNP.Source284GuardRowCoreTM2
