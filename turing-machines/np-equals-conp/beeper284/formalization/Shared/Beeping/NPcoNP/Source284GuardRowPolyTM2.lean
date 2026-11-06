import Shared.Beeping.NPcoNP.Source284GuardRow
import Shared.Beeping.NPcoNP.Source284GuardRowCoreTM2
import Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2
import Shared.ComplexityBridge.TM2CircuitOutputWorker

/-! Canonical polynomial-time construction of one guarded encoded row from
an explicitly supplied finite row list and unary cutoff. Every lookup and
bounded pairing is charged; no function-valued original table is an input.
This module does not construct the full output list or prove SAT hardness. -/
namespace Shared.Beeping.NPcoNP.Source284GuardRowPolyTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284GuardRow
open Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2

private theorem outer_first : IsPolyTime (fun p : Input => p.1) := TM2PairFirst.first_isPolyTime
private theorem outer_second : IsPolyTime (fun p : Input => p.2) := TM2GuardAllStep.second_isPolyTime
private theorem cutoff_poly : IsPolyTime (fun p : Input => p.1.1) :=
  TM2Compose.isPolyTime_comp (fun p : Input => p.1) (fun p : List Bool × EncRows => p.1)
    outer_first TM2PairFirst.first_isPolyTime
private theorem rows_poly : IsPolyTime (fun p : Input => p.1.2) :=
  TM2Compose.isPolyTime_comp (fun p : Input => p.1) (fun p : List Bool × EncRows => p.2)
    outer_first TM2GuardAllStep.second_isPolyTime
private theorem state_poly : IsPolyTime (fun p : Input => p.2.1) :=
  TM2Compose.isPolyTime_comp (fun p : Input => p.2) (fun p : Nat × Bool => p.1)
    outer_second TM2PairFirst.first_isPolyTime
private theorem read_poly : IsPolyTime (fun p : Input => p.2.2) :=
  TM2Compose.isPolyTime_comp (fun p : Input => p.2) (fun p : Nat × Bool => p.2)
    outer_second TM2GuardAllStep.second_isPolyTime
private theorem tokens_poly : IsPolyTime (fun p : Input => nTokens p.1.2) :=
  TM2Compose.isPolyTime_comp (fun p : Input => p.1.2) nTokens rows_poly
    TM2ListUnaryLength.unaryLength_isPolyTime

theorem selection_isPolyTime : IsPolyTime selection := by
  have hb := TM2GuardAllStep.pair_isPolyTime (fun p : Input => nTokens p.1.2)
    (fun p => p.1.1) tokens_poly cutoff_poly
  have ha := TM2GuardAllStep.pair_isPolyTime
    (fun p : Input => (nTokens p.1.2,p.1.1)) (fun p => p.2.1) hb state_poly
  exact TM2Compose.isPolyTime_comp (fun p : Input => ((nTokens p.1.2,p.1.1),p.2.1))
    Source284SearchSelectTM2.select ha Source284SearchSelectTM2.select_isPolyTime

private theorem zero_poly : IsPolyTime (fun _ : Input => (0 : Nat)) := TM2EmptyConstant.zero_isPolyTime
private theorem false_poly : IsPolyTime (fun _ : Input => false) := TM2Constant.isPolyTime false
private theorem true_poly : IsPolyTime (fun _ : Input => true) := TM2Constant.isPolyTime true
private theorem default_poly : IsPolyTime (fun _ : Input => defaultPair) := by
  have hr : IsPolyTime (fun _ : Input => ((false,false,false,0) : EncRow)) :=
    row_isPolyTime _ _ _ _ false_poly false_poly false_poly zero_poly
  exact TM2GuardAllStep.pair_isPolyTime _ _ hr hr

theorem selectedPair_isPolyTime : IsPolyTime selectedPair := by
  let result : Input → Source284SearchSelectTM2.Result := selection
  let coord : Input → Nat × Nat := fun p => (result p).2
  let index : Input → Nat := fun p => (coord p).2
  have hc : IsPolyTime coord := TM2Compose.isPolyTime_comp result
    (fun r : Source284SearchSelectTM2.Result => r.2) selection_isPolyTime TM2GuardAllStep.second_isPolyTime
  have hi : IsPolyTime index := TM2Compose.isPolyTime_comp coord (fun p : Nat × Nat => p.2)
    hc TM2GuardAllStep.second_isPolyTime
  have hargs := TM2GuardAllStep.pair_isPolyTime (fun p : Input => p.1.2)
    (fun p => (index p,defaultPair)) rows_poly
      (TM2GuardAllStep.pair_isPolyTime index (fun _ => defaultPair) hi default_poly)
  exact TM2Compose.isPolyTime_comp (fun p : Input => (p.1.2,(index p,defaultPair)))
    (TM2ListLookup.lookup (β := EncRow × EncRow)) hargs TM2ListLookup.lookup_isPolyTime

theorem selectedRow_isPolyTime : IsPolyTime selectedRow := by
  let r : Input → EncRow × EncRow := selectedPair
  let first : Input → EncRow := fun p => (r p).1
  let second : Input → EncRow := fun p => (r p).2
  have h1 : IsPolyTime first := TM2Compose.isPolyTime_comp r (fun x : EncRow × EncRow => x.1)
    selectedPair_isPolyTime TM2PairFirst.first_isPolyTime
  have h2 : IsPolyTime second := TM2Compose.isPolyTime_comp r (fun x : EncRow × EncRow => x.2)
    selectedPair_isPolyTime TM2GuardAllStep.second_isPolyTime
  exact TM2If.if_isPolyTime (fun p : Input => p.2.2) second first read_poly h2 h1

theorem sinkCode_isPolyTime : IsPolyTime (fun p : Input => sinkCode p.1.1 p.1.2) := by
  let b : Input → List Bool × List Bool := fun p => (p.1.1,nTokens p.1.2)
  have hb : IsPolyTime b := TM2GuardAllStep.pair_isPolyTime (fun p : Input => p.1.1)
    (fun p => nTokens p.1.2) cutoff_poly tokens_poly
  have h := TM2Compose.isPolyTime_comp b Source284GuardRowCoreTM2.sink hb Source284GuardRowCoreTM2.sink_isPolyTime
  simpa [b, Source284GuardRowCoreTM2.sink, sinkCode, budget] using h

theorem guardedRow_isPolyTime : IsPolyTime guardedRow := by
  let result : Input → Source284SearchSelectTM2.Result := selection
  let flag : Input → Bool := fun p => (result p).1
  let coord : Input → Nat × Nat := fun p => (result p).2
  let elapsed : Input → Nat := fun p => (coord p).1
  let coreArg : Input → Source284GuardRowCoreTM2.Input := fun p =>
    (p.1.1,(nTokens p.1.2,(elapsed p,selectedRow p)))
  let live : Input → EncRow := fun p => Source284GuardRowCoreTM2.core (coreArg p)
  let dead : Input → EncRow := fun p => sinkRow p.1.1 p.1.2 p.2.2
  have hf : IsPolyTime flag := TM2Compose.isPolyTime_comp result
    (fun r : Source284SearchSelectTM2.Result => r.1) selection_isPolyTime TM2PairFirst.first_isPolyTime
  have hc : IsPolyTime coord := TM2Compose.isPolyTime_comp result
    (fun r : Source284SearchSelectTM2.Result => r.2) selection_isPolyTime TM2GuardAllStep.second_isPolyTime
  have he : IsPolyTime elapsed := TM2Compose.isPolyTime_comp coord
    (fun r : Nat × Nat => r.1) hc TM2PairFirst.first_isPolyTime
  have ha : IsPolyTime coreArg := TM2GuardAllStep.pair_isPolyTime
    (fun p : Input => p.1.1) (fun p => (nTokens p.1.2,(elapsed p,selectedRow p))) cutoff_poly
    (TM2GuardAllStep.pair_isPolyTime (fun p => nTokens p.1.2) (fun p => (elapsed p,selectedRow p))
      tokens_poly (TM2GuardAllStep.pair_isPolyTime elapsed selectedRow he selectedRow_isPolyTime))
  have hl : IsPolyTime live := TM2Compose.isPolyTime_comp coreArg Source284GuardRowCoreTM2.core
    ha Source284GuardRowCoreTM2.core_isPolyTime
  have hd : IsPolyTime dead := by
    have h := row_isPolyTime (fun p : Input => p.2.2) (fun _ => false) (fun _ => true)
      (fun p => sinkCode p.1.1 p.1.2) read_poly false_poly true_poly sinkCode_isPolyTime
    exact h
  have h := TM2If.if_isPolyTime flag live dead hf hl hd
  have heq : (fun p => if flag p then live p else dead p) = guardedRow := by
    funext p
    cases hr : (selectedRow p).2.2.1 <;>
      simp [guardedRow, live, dead, coreArg, elapsed, coord, result, flag,
        Source284GuardRowCoreTM2.core, Source284GuardRowCoreTM2.writeBit,
        Source284GuardRowCoreTM2.turnBit, Source284GuardRowCoreTM2.continues,
        Source284GuardRowCoreTM2.destination, Source284GuardRowCoreTM2.target,
        Source284GuardRowCoreTM2.active, Source284GuardRowCoreTM2.cutoff,
        Source284GuardRowCoreTM2.states, Source284GuardRowCoreTM2.elapsed,
        Source284GuardRowCoreTM2.original, Source284GuardRowCoreTM2.budget,
        Source284GuardRowCoreTM2.nextElapsed, Source284GuardRowCoreTM2.oldDest,
        Source284GuardRowCoreTM2.sink, sinkRow, sinkCode, destination, nextLive, budget, hr]
  rw [heq] at h
  exact h

end Shared.Beeping.NPcoNP.Source284GuardRowPolyTM2
