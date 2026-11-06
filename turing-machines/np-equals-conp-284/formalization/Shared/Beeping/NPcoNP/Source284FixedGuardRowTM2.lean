import Shared.Beeping.NPcoNP.Source284FixedGuardForwardTM2

/-! Canonical polynomial-time construction of every row of the fixed-window
guard, including its scan, turn, rewind, handoff, and reject rows. The
witness limit is supplied in unary; this is a row worker, not yet a
whole-table generator or an input-dependent source program. -/
namespace Shared.Beeping.NPcoNP.Source284FixedGuardRowTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284FixedGuardForwardTM2

/-- Concatenation with a fixed number of copies is charged linearly in the
unary list length. -/
def copies : Nat → List Bool → List Bool
  | 0, _ => []
  | k+1, xs => xs ++ copies k xs

theorem copies_length (k : Nat) (xs : List Bool) : (copies k xs).length = k*xs.length := by
  induction k with
  | zero => simp [copies]
  | succ k ih => simp [copies,ih,Nat.succ_mul]; omega

theorem copies_isPolyTime (k : Nat) : IsPolyTime (copies k) := by
  induction k with
  | zero => exact TM2EmptyConstant.isPolyTime [] rfl
  | succ k ih =>
    let identity : List Bool → List Bool := id
    have hi : IsPolyTime identity := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
    have h := TM2Compose.isPolyTime_comp (fun xs : List Bool => (identity xs,copies k xs))
      (TM2ListAppend.append (α := Bool)) (TM2GuardAllStep.pair_isPolyTime identity _ hi ih)
      TM2ListAppend.append_isPolyTime
    have he : (fun xs : List Bool => TM2ListAppend.append (identity xs,copies k xs)) = copies (k+1) := by
      funext xs
      rfl
    rw [← he]
    exact h

def liveTokens (xs : List Bool) : List Bool := copies 7 (ticks xs)
def startTokens (xs : List Bool) : List Bool := liveTokens xs ++ [true,true]
def endTokens (xs : List Bool) : List Bool := copies 8 (ticks xs) ++ [true]

theorem liveTokens_length (xs : List Bool) :
    (liveTokens xs).length = Source284FixedGuardRewind.rewindTurn xs.length := by
  simp [liveTokens,copies_length,ticks_length,Source284FixedGuardRewind.rewindTurn]

theorem startTokens_length (xs : List Bool) :
    (startTokens xs).length = Source284FixedGuardRewind.rewindStart xs.length := by
  simp [startTokens,liveTokens_length,Source284FixedGuardRewind.rewindStart]

theorem endTokens_length (xs : List Bool) :
    (endTokens xs).length = Source284FixedGuardRewind.handoff xs.length := by
  simp [endTokens,copies_length,ticks_length,Source284FixedGuardRewind.handoff,
    Source284FixedGuardRewind.rewindStart,Source284FixedGuardRewind.rewindTurn,
    Source284FixedGuardRewind.width,Source284FixedWitnessGuard.cutoff]
  omega

private theorem liveTokens_isPolyTime : IsPolyTime liveTokens :=
  TM2Compose.isPolyTime_comp ticks (copies 7) ticks_isPolyTime (copies_isPolyTime 7)

theorem addSingleton_isPolyTime : IsPolyTime (fun xs : List Bool => xs ++ [true]) := by
  have hi : IsPolyTime (id : List Bool → List Bool) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have ht : IsPolyTime (fun _ : List Bool => true) := TM2Constant.isPolyTime true
  have hs : IsPolyTime (fun _ : List Bool => [true]) := TM2GateCNFPieces.singleton_isPolyTime _ ht
  have h := TM2Compose.isPolyTime_comp (fun xs : List Bool => (xs,[true]))
    (TM2ListAppend.append (α := Bool)) (TM2GuardAllStep.pair_isPolyTime _ _ hi hs)
    TM2ListAppend.append_isPolyTime
  exact h

private theorem startTokens_isPolyTime : IsPolyTime startTokens := by
  have h := TM2Compose.isPolyTime_comp liveTokens (fun xs : List Bool => xs++[true])
    liveTokens_isPolyTime addSingleton_isPolyTime
  have hh := TM2Compose.isPolyTime_comp (fun xs : List Bool => liveTokens xs++[true])
    (fun xs : List Bool => xs++[true]) h addSingleton_isPolyTime
  have he : (fun xs : List Bool => (liveTokens xs++[true])++[true]) = startTokens := by
    funext xs; simp [startTokens]
  rwa [he] at hh

theorem endTokens_isPolyTime : IsPolyTime endTokens := by
  have h := TM2Compose.isPolyTime_comp ticks (copies 8) ticks_isPolyTime (copies_isPolyTime 8)
  exact TM2Compose.isPolyTime_comp (fun xs : List Bool => copies 8 (ticks xs))
    (fun xs : List Bool => xs++[true]) h addSingleton_isPolyTime

def query (p : Input) : Nat := p.1.2
def tokenInput (p : Input) : List Bool := p.1.1

def inLive (p : Input) : Bool := TM2BoundedWitnessGuard.guard (liveTokens (tokenInput p),query p)
def atTurn (p : Input) : Bool := !TM2BoundedWitnessGuard.numericNe (query p,boundary p)
def beforeStart (p : Input) : Bool := TM2BoundedWitnessGuard.guard (startTokens (tokenInput p),query p)
def beforeEnd (p : Input) : Bool := TM2BoundedWitnessGuard.guard (endTokens (tokenInput p),query p)
def inRewind (p : Input) : Bool := !beforeStart p && beforeEnd p

def startDest (p : Input) : Nat := boundary p+2
def nextDest (p : Input) : Nat := query p+1
def sinkDest (p : Input) : Nat := boundary p+1

def turnRow (p : Input) : EncRow := (read p,true,true,startDest p)
def rewindRow (p : Input) : EncRow := (read p,false,true,nextDest p)
def sinkRow (p : Input) : EncRow := (read p,false,true,sinkDest p)

def row (p : Input) : EncRow :=
  if inLive p then Source284FixedGuardForwardTM2.row p
  else if atTurn p then turnRow p
  else if inRewind p then rewindRow p else sinkRow p

private theorem query_isPolyTime : IsPolyTime query := by
  exact TM2Compose.isPolyTime_comp (fun p : Input => p.1) (fun p : List Bool × Nat => p.2)
    TM2PairFirst.first_isPolyTime TM2GuardAllStep.second_isPolyTime
private theorem tokenInput_isPolyTime : IsPolyTime tokenInput := by
  exact TM2Compose.isPolyTime_comp (fun p : Input => p.1) (fun p : List Bool × Nat => p.1)
    TM2PairFirst.first_isPolyTime TM2PairFirst.first_isPolyTime

private theorem guard_isPolyTime (f : List Bool → List Bool) (hf : IsPolyTime f) :
    IsPolyTime (fun p : Input => TM2BoundedWitnessGuard.guard (f (tokenInput p),query p)) := by
  have htokens : IsPolyTime (fun p : Input => f (tokenInput p)) :=
    TM2Compose.isPolyTime_comp tokenInput f tokenInput_isPolyTime hf
  exact TM2Compose.isPolyTime_comp (fun p : Input => (f (tokenInput p),query p))
    TM2BoundedWitnessGuard.guard (TM2GuardAllStep.pair_isPolyTime _ _ htokens query_isPolyTime)
    TM2BoundedWitnessGuard.guard_isPolyTime

private theorem inLive_isPolyTime : IsPolyTime inLive := guard_isPolyTime liveTokens liveTokens_isPolyTime
private theorem beforeStart_isPolyTime : IsPolyTime beforeStart := guard_isPolyTime startTokens startTokens_isPolyTime
private theorem beforeEnd_isPolyTime : IsPolyTime beforeEnd := guard_isPolyTime endTokens endTokens_isPolyTime
private theorem atTurn_isPolyTime : IsPolyTime atTurn := by
  have hn := TM2Compose.isPolyTime_comp (fun p : Input => (query p,boundary p))
    TM2BoundedWitnessGuard.numericNe
    (TM2GuardAllStep.pair_isPolyTime query boundary query_isPolyTime boundary_isPolyTime)
    TM2BoundedWitnessGuard.numericNe_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p : Input => TM2BoundedWitnessGuard.numericNe (query p,boundary p))
    Bool.not hn TM2GateDispatch.not_isPolyTime
private theorem inRewind_isPolyTime : IsPolyTime inRewind := by
  have hn : IsPolyTime (fun p : Input => !beforeStart p) :=
    TM2Compose.isPolyTime_comp beforeStart Bool.not beforeStart_isPolyTime TM2GateDispatch.not_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p : Input => (!beforeStart p,beforeEnd p))
    (fun p : Bool × Bool => p.1 && p.2)
    (TM2GuardAllStep.pair_isPolyTime _ _ hn beforeEnd_isPolyTime) TM2GateDispatch.and_isPolyTime
private theorem startDest_isPolyTime : IsPolyTime startDest :=
  TM2Compose.isPolyTime_comp boundary (fun x : Nat => x+2) boundary_isPolyTime (TM2FixedRows.addFixed_isPolyTime 2)
private theorem nextDest_isPolyTime : IsPolyTime nextDest :=
  TM2Compose.isPolyTime_comp query (fun x : Nat => x+1) query_isPolyTime (TM2FixedRows.addFixed_isPolyTime 1)
private theorem sinkDest_isPolyTime : IsPolyTime sinkDest :=
  TM2Compose.isPolyTime_comp boundary (fun x : Nat => x+1) boundary_isPolyTime (TM2FixedRows.addFixed_isPolyTime 1)

private theorem branch_isPolyTime (turnBit : Bool) (destination : Input → Nat)
    (hd : IsPolyTime destination) : IsPolyTime (fun p => (read p,turnBit,true,destination p) : Input → EncRow) := by
  exact Source284HardwireEncodedWorkersTM2.row_isPolyTime read (fun _ => turnBit) (fun _ => true) destination
    read_isPolyTime (TM2Constant.isPolyTime turnBit) (TM2Constant.isPolyTime true) hd

theorem row_isPolyTime : IsPolyTime row := by
  have ht : IsPolyTime turnRow := branch_isPolyTime true startDest startDest_isPolyTime
  have hr : IsPolyTime rewindRow := branch_isPolyTime false nextDest nextDest_isPolyTime
  have hs : IsPolyTime sinkRow := branch_isPolyTime false sinkDest sinkDest_isPolyTime
  have hrewind := TM2If.if_isPolyTime inRewind rewindRow sinkRow inRewind_isPolyTime hr hs
  have hturn := TM2If.if_isPolyTime atTurn turnRow (fun p => if inRewind p then rewindRow p else sinkRow p)
    atTurn_isPolyTime ht hrewind
  exact TM2If.if_isPolyTime inLive Source284FixedGuardForwardTM2.row
    (fun p => if atTurn p then turnRow p else if inRewind p then rewindRow p else sinkRow p)
    inLive_isPolyTime Source284FixedGuardForwardTM2.row_isPolyTime hturn

theorem row_correct (tokens : List Bool) (q : Nat) (b : Bool) :
    decodeRow (row ((tokens,q),b)) = Source284FixedGuardRewind.table tokens.length q b := by
  have hlive : inLive ((tokens,q),b) = decide (q < Source284FixedGuardRewind.rewindTurn tokens.length) := by
    simp [inLive,tokenInput,query,TM2TapePairs.guard_eq_decide,liveTokens_length]
  have hstart : beforeStart ((tokens,q),b) = decide (q < Source284FixedGuardRewind.rewindStart tokens.length) := by
    simp [beforeStart,tokenInput,query,TM2TapePairs.guard_eq_decide,startTokens_length]
  have hend : beforeEnd ((tokens,q),b) = decide (q < Source284FixedGuardRewind.handoff tokens.length) := by
    simp [beforeEnd,tokenInput,query,TM2TapePairs.guard_eq_decide,endTokens_length]
  have hboundary : boundary ((tokens,q),b) = Source284FixedGuardRewind.rewindTurn tokens.length := by
    simp [boundary,Source284FixedBaseSearchTM2.code,ticks_length,Source284FixedGuardRewind.rewindTurn]
  have hturn : atTurn ((tokens,q),b) = decide (q = Source284FixedGuardRewind.rewindTurn tokens.length) := by
    by_cases h : q = 7*Source284FixedWitnessGuard.cutoff tokens.length <;>
      simp [atTurn,query,boundary,Source284FixedBaseSearchTM2.code,ticks_length,
        Source284FixedGuardRewind.rewindTurn,TM2BoundedWitnessGuard.numericNe,h]
  by_cases hf : q < Source284FixedGuardRewind.rewindTurn tokens.length
  · simpa [row,hlive,hf] using Source284FixedGuardForwardTM2.row_correct tokens q b hf
  · by_cases ht : q = Source284FixedGuardRewind.rewindTurn tokens.length
    · have hv : inLive ((tokens,q),b) = false := by rw [hlive]; simp [hf]
      have ha : atTurn ((tokens,q),b) = true := by rw [hturn]; simp [ht]
      simp only [row,hv,Bool.false_eq_true,↓reduceIte,ha]
      unfold Source284FixedGuardRewind.table
      simp only [hf,↓reduceIte,ht]
      simp [turnRow,Source284FixedGuardForwardTM2.read,startDest,boundary,
        Source284FixedBaseSearchTM2.code,ticks_length,Source284FixedGuardRewind.rewindTurn,
        Source284FixedGuardRewind.rewindStart,decodeRow]
    · by_cases hr : Source284FixedGuardRewind.rewindStart tokens.length ≤ q ∧
          q < Source284FixedGuardRewind.handoff tokens.length
      · have hs : ¬ q < Source284FixedGuardRewind.rewindStart tokens.length := by omega
        have he : q < Source284FixedGuardRewind.handoff tokens.length := hr.2
        simp [row,hlive,hf,hturn,ht,inRewind,hstart,hend,hs,he,rewindRow,Source284FixedGuardForwardTM2.read,nextDest,query,
          Source284FixedGuardRewind.table,hr,decodeRow]
      · by_cases hs : q < Source284FixedGuardRewind.rewindStart tokens.length
        · simp [row,hlive,hf,hturn,ht,inRewind,hstart,hs,sinkRow,Source284FixedGuardForwardTM2.read,sinkDest,query,hboundary,
            Source284FixedGuardRewind.table,hr,Source284FixedGuardRewind.sink,decodeRow]
        · have he : ¬ q < Source284FixedGuardRewind.handoff tokens.length := by omega
          simp [row,hlive,hf,hturn,ht,inRewind,hstart,hend,hs,he,sinkRow,Source284FixedGuardForwardTM2.read,sinkDest,query,hboundary,
            Source284FixedGuardRewind.table,hr,Source284FixedGuardRewind.sink,decodeRow]

end Shared.Beeping.NPcoNP.Source284FixedGuardRowTM2
