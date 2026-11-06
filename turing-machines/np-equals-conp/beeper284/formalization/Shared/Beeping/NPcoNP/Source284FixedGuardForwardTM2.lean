import Shared.Beeping.NPcoNP.Source284FixedBaseSearchTM2
import Shared.Beeping.NPcoNP.Source284TaggedScannerNextTM2
import Shared.Beeping.NPcoNP.Source284FixedGuardRewind

/-! Polynomial-time construction of a live forward row of the fixed-window
guard. The witness limit is supplied in unary, and the binary row index is
searched only inside the charged unary rectangle. Out-of-range requests have
a total default and are not claimed to match the other guard branches. -/
namespace Shared.Beeping.NPcoNP.Source284FixedGuardForwardTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows

abbrev Input := (List Bool × Nat) × Bool

def ticks (tokens : List Bool) : List Bool :=
  tokens ++ tokens ++ [true,true,true,true]

theorem ticks_length (tokens : List Bool) :
    (ticks tokens).length = Source284FixedWitnessGuard.cutoff tokens.length := by
  simp [ticks,Source284FixedWitnessGuard.cutoff]
  omega

theorem ticks_isPolyTime : IsPolyTime ticks := by
  let idb : List Bool → List Bool := id
  let twice : List Bool → List Bool := fun xs => xs++xs
  let four : List Bool → List Bool := fun _ => [true,true,true,true]
  have hi : IsPolyTime idb := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have htwice : IsPolyTime twice := TM2Compose.isPolyTime_comp (fun xs : List Bool => (idb xs,idb xs))
    (TM2ListAppend.append (α := Bool)) (TM2GuardAllStep.pair_isPolyTime idb idb hi hi)
    TM2ListAppend.append_isPolyTime
  have hfour : IsPolyTime four := by
    have h := TM2UnaryPolynomialIO.unaryPolynomial_isPolyTime (Polynomial.C 4)
    have he : TM2UnaryPolynomialIO.unaryPolynomial (Polynomial.C 4) = four := by
      funext xs
      simp [four,TM2UnaryPolynomialIO.unaryPolynomial]
    rw [← he]
    exact h
  have h := TM2Compose.isPolyTime_comp (fun xs : List Bool => (twice xs,four xs))
    (TM2ListAppend.append (α := Bool)) (TM2GuardAllStep.pair_isPolyTime twice four htwice hfour)
    TM2ListAppend.append_isPolyTime
  have he : (fun xs : List Bool => TM2ListAppend.append (twice xs,four xs)) = ticks := by
    funext xs
    simp [ticks,twice,four,TM2ListAppend.append]
  rw [← he]
  exact h

def coordinates (p : Input) : Nat × Nat :=
  Source284FixedBaseSearchTM2.select 7 (ticks p.1.1,p.1.2)

theorem coordinates_isPolyTime : IsPolyTime coordinates := by
  let first : Input → List Bool × Nat := fun p => p.1
  let tokens : Input → List Bool := fun p => p.1.1
  let query : Input → Nat := fun p => p.1.2
  have hf : IsPolyTime first := TM2PairFirst.first_isPolyTime
  have ht : IsPolyTime tokens := TM2Compose.isPolyTime_comp first (fun p : List Bool × Nat => p.1)
    hf TM2PairFirst.first_isPolyTime
  have hq : IsPolyTime query := TM2Compose.isPolyTime_comp first (fun p : List Bool × Nat => p.2)
    hf TM2GuardAllStep.second_isPolyTime
  have hk : IsPolyTime (fun p : Input => ticks (tokens p)) :=
    TM2Compose.isPolyTime_comp tokens ticks ht ticks_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p : Input => (ticks (tokens p),query p))
    (Source284FixedBaseSearchTM2.select 7)
    (TM2GuardAllStep.pair_isPolyTime _ _ hk hq)
    (Source284FixedBaseSearchTM2.select_isPolyTime 7)

def elapsed (p : Input) : Nat := (coordinates p).1
def mode (p : Input) : Nat := (coordinates p).2
def read (p : Input) : Bool := p.2
def nextMode (p : Input) : Nat := Source284TaggedScannerNextTM2.next (mode p,read p)
def turn (p : Input) : Bool := Source284TaggedScannerNextTM2.turn (mode p,read p)
def nextElapsed (p : Input) : Nat := elapsed p+1
def live (p : Input) : Bool := TM2BoundedWitnessGuard.guard (ticks p.1.1,nextElapsed p)
def isCompleted (p : Input) : Bool := !TM2BoundedWitnessGuard.numericNe (nextMode p,3)
def boundary (p : Input) : Nat := Source284FixedBaseSearchTM2.code 7 ((ticks p.1.1).length,0)
def forwardDest (p : Input) : Nat := Source284FixedBaseSearchTM2.code 7 (nextElapsed p,nextMode p)
def destination (p : Input) : Nat :=
  if live p then forwardDest p else if isCompleted p then boundary p else boundary p+1

def row (p : Input) : EncRow := (read p,turn p,true,destination p)

private theorem fst_isPolyTime : IsPolyTime (fun p : Input => p.1) := TM2PairFirst.first_isPolyTime
private theorem tokens_isPolyTime : IsPolyTime (fun p : Input => p.1.1) :=
  TM2Compose.isPolyTime_comp (fun p : Input => p.1) (fun p : List Bool × Nat => p.1)
    fst_isPolyTime TM2PairFirst.first_isPolyTime
theorem ticksInput_isPolyTime : IsPolyTime (fun p : Input => ticks p.1.1) :=
  TM2Compose.isPolyTime_comp (fun p : Input => p.1.1) ticks tokens_isPolyTime ticks_isPolyTime
private theorem elapsed_isPolyTime : IsPolyTime elapsed :=
  TM2Compose.isPolyTime_comp coordinates (fun p : Nat × Nat => p.1)
    coordinates_isPolyTime TM2PairFirst.first_isPolyTime
private theorem mode_isPolyTime : IsPolyTime mode :=
  TM2Compose.isPolyTime_comp coordinates (fun p : Nat × Nat => p.2)
    coordinates_isPolyTime TM2GuardAllStep.second_isPolyTime
theorem read_isPolyTime : IsPolyTime read := TM2GuardAllStep.second_isPolyTime
private theorem modeRead_isPolyTime : IsPolyTime (fun p : Input => (mode p,read p)) :=
  TM2GuardAllStep.pair_isPolyTime mode read mode_isPolyTime read_isPolyTime
private theorem nextMode_isPolyTime : IsPolyTime nextMode :=
  TM2Compose.isPolyTime_comp (fun p : Input => (mode p,read p)) Source284TaggedScannerNextTM2.next
    modeRead_isPolyTime Source284TaggedScannerNextTM2.next_isPolyTime
private theorem turn_isPolyTime : IsPolyTime turn :=
  TM2Compose.isPolyTime_comp (fun p : Input => (mode p,read p)) Source284TaggedScannerNextTM2.turn
    modeRead_isPolyTime Source284TaggedScannerNextTM2.turn_isPolyTime
private theorem nextElapsed_isPolyTime : IsPolyTime nextElapsed :=
  TM2Compose.isPolyTime_comp elapsed (fun n : Nat => n+1) elapsed_isPolyTime
    (TM2FixedRows.addFixed_isPolyTime 1)
private theorem live_isPolyTime : IsPolyTime live := by
  exact TM2Compose.isPolyTime_comp (fun p : Input => (ticks p.1.1,nextElapsed p))
    TM2BoundedWitnessGuard.guard
    (TM2GuardAllStep.pair_isPolyTime _ _ ticksInput_isPolyTime nextElapsed_isPolyTime)
    TM2BoundedWitnessGuard.guard_isPolyTime
private theorem isCompleted_isPolyTime : IsPolyTime isCompleted := by
  let three : Input → Nat := fun _ => 3
  have hz : IsPolyTime (fun _ : Input => (0 : Nat)) := TM2EmptyConstant.zero_isPolyTime
  have h3 : IsPolyTime three := by
    have h := TM2Compose.isPolyTime_comp (fun _ : Input => (0 : Nat)) (fun x : Nat => x+3)
      hz (TM2FixedRows.addFixed_isPolyTime 3)
    simpa [three] using h
  have hne := TM2Compose.isPolyTime_comp (fun p : Input => (nextMode p,three p))
    TM2BoundedWitnessGuard.numericNe (TM2GuardAllStep.pair_isPolyTime _ _ nextMode_isPolyTime h3)
    TM2BoundedWitnessGuard.numericNe_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p : Input => TM2BoundedWitnessGuard.numericNe (nextMode p,3))
    Bool.not hne TM2GateDispatch.not_isPolyTime
theorem boundary_isPolyTime : IsPolyTime boundary := by
  have hlen : IsPolyTime (fun p : Input => (ticks p.1.1).length) :=
    TM2Compose.isPolyTime_comp (fun p : Input => ticks p.1.1) List.length
      ticksInput_isPolyTime TM2BinaryListLength.length_isPolyTime
  have hz : IsPolyTime (fun _ : Input => (0 : Nat)) := TM2EmptyConstant.zero_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p : Input => ((ticks p.1.1).length,0))
    (Source284FixedBaseSearchTM2.code 7) (TM2GuardAllStep.pair_isPolyTime _ _ hlen hz)
    (Source284FixedBaseSearchTM2.code_isPolyTime 7)
private theorem forwardDest_isPolyTime : IsPolyTime forwardDest :=
  TM2Compose.isPolyTime_comp (fun p : Input => (nextElapsed p,nextMode p))
    (Source284FixedBaseSearchTM2.code 7)
    (TM2GuardAllStep.pair_isPolyTime _ _ nextElapsed_isPolyTime nextMode_isPolyTime)
    (Source284FixedBaseSearchTM2.code_isPolyTime 7)
private theorem destination_isPolyTime : IsPolyTime destination := by
  have hplus : IsPolyTime (fun p : Input => boundary p+1) :=
    TM2Compose.isPolyTime_comp boundary (fun x : Nat => x+1) boundary_isPolyTime
      (TM2FixedRows.addFixed_isPolyTime 1)
  have hlast := TM2If.if_isPolyTime isCompleted boundary (fun p : Input => boundary p+1)
    isCompleted_isPolyTime boundary_isPolyTime hplus
  exact TM2If.if_isPolyTime live forwardDest
    (fun p : Input => if isCompleted p then boundary p else boundary p+1)
    live_isPolyTime forwardDest_isPolyTime hlast

theorem row_isPolyTime : IsPolyTime row := by
  have ht : IsPolyTime (fun _ : Input => true) := TM2Constant.isPolyTime true
  exact Source284HardwireEncodedWorkersTM2.row_isPolyTime read turn (fun _ => true) destination
    read_isPolyTime turn_isPolyTime ht destination_isPolyTime

/-- Every live forward row is exactly the existing source guard's row; the
other guard phases are intentionally outside this branch. -/
theorem row_correct (tokens : List Bool) (q : Nat) (b : Bool)
    (hq : q < Source284FixedGuardRewind.rewindTurn tokens.length) :
    decodeRow (row ((tokens,q),b)) = Source284FixedGuardRewind.table tokens.length q b := by
  have hq' : q < 7*(ticks tokens).length := by
    simpa [ticks_length,Source284FixedGuardRewind.rewindTurn] using hq
  have hcoord := Source284FixedBaseSearchTM2.select_correct 7 (ticks tokens) q (by decide) hq'
  have hticks : (ticks tokens).length = Source284FixedWitnessGuard.cutoff tokens.length := ticks_length tokens
  have hmode : mode ((tokens,q),b) = q%7 := by simp [mode,coordinates,hcoord]
  have helapsed : elapsed ((tokens,q),b) = q/7 := by simp [elapsed,coordinates,hcoord]
  have hnext : nextMode ((tokens,q),b) =
      (Source284TaggedScanner.table (q%7) b).next.getD 6 := by
    rw [nextMode,hmode,show read ((tokens,q),b) = b by rfl,
      Source284TaggedScannerNextTM2.next_correct]
    rfl
  have hturn : turn ((tokens,q),b) = (Source284TaggedScanner.table (q%7) b).turn := by
    rw [turn,hmode,show read ((tokens,q),b) = b by rfl]
    exact (Source284TaggedScannerNextTM2.turn_correct _ _).symm
  have hwrite : (Source284TaggedScanner.table (q%7) b).write = b := by
    have hm := Nat.mod_lt q (by decide : 0 < 7)
    generalize q%7 = mode at *
    interval_cases mode <;> cases b <;> rfl
  have hlive : live ((tokens,q),b) = decide (q/7+1 < Source284FixedWitnessGuard.cutoff tokens.length) := by
    simp [live,nextElapsed,helapsed,TM2TapePairs.guard_eq_decide,hticks]
  simp only [row,decodeRow,read,hturn]
  unfold Source284FixedGuardRewind.table
  simp only [hq,↓reduceIte]
  simp [destination,hlive,isCompleted,hnext,TM2BoundedWitnessGuard.numericNe,
    forwardDest,boundary,nextElapsed,helapsed,hticks,Source284FixedBaseSearchTM2.code,
    Source284FixedGuardRewind.code,Source284FixedGuardRewind.rewindTurn,Source284FixedGuardRewind.sink,
    hwrite]

end Shared.Beeping.NPcoNP.Source284FixedGuardForwardTM2
