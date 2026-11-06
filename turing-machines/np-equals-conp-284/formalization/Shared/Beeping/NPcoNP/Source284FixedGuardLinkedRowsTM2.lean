import Shared.Beeping.NPcoNP.Source284FixedGuardRowsTM2
import Shared.Beeping.NPcoNP.Source284FixedGuardLink
import Shared.Beeping.NPcoNP.Source284RowNormalizationTM2

/-! Polynomial construction of the finite fixed guard linked to an explicit
finite verifier table. The unary limit and the entire encoded verifier list
are charged. This module does not construct the verifier or a dynamic source
program. -/
namespace Shared.Beeping.NPcoNP.Source284FixedGuardLinkedRowsTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2 (shiftPair shiftPair_isPolyTime)

abbrev Input := List Bool × EncRows
abbrev Request := Input × Nat

def guardCount (tokens : List Bool) : Nat := (Source284FixedGuardRowsTM2.stateTokens tokens).length

def handoff (tokens : List Bool) : Nat := (Source284FixedGuardRowTM2.endTokens tokens).length

@[simp] theorem guardCount_eq (tokens : List Bool) :
    guardCount tokens = Source284FixedGuardRewind.states tokens.length :=
  Source284FixedGuardRowsTM2.stateTokens_length tokens

@[simp] theorem handoff_eq (tokens : List Bool) :
    handoff tokens = Source284FixedGuardRewind.handoff tokens.length :=
  Source284FixedGuardRowTM2.endTokens_length tokens

theorem guardCount_isPolyTime : IsPolyTime guardCount :=
  TM2Compose.isPolyTime_comp Source284FixedGuardRowsTM2.stateTokens List.length
    Source284FixedGuardRowsTM2.stateTokens_isPolyTime TM2BinaryListLength.length_isPolyTime

theorem handoff_isPolyTime : IsPolyTime handoff :=
  TM2Compose.isPolyTime_comp Source284FixedGuardRowTM2.endTokens List.length
    Source284FixedGuardRowTM2.endTokens_isPolyTime TM2BinaryListLength.length_isPolyTime

def firstShift (p : Input) : EncRow × EncRow :=
  shiftPair (guardCount p.1,Source284RowNormalizationTM2.lookupPair (p.2,0))

theorem firstShift_isPolyTime : IsPolyTime firstShift := by
  let tokens : Input → List Bool := fun p => p.1
  let original : Input → EncRows := fun p => p.2
  let offset : Input → Nat := fun p => guardCount (tokens p)
  let zero : Input → Nat := fun _ => 0
  let first : Input → EncRow × EncRow := fun p => Source284RowNormalizationTM2.lookupPair (original p,zero p)
  have ht : IsPolyTime tokens := TM2PairFirst.first_isPolyTime
  have hr : IsPolyTime original := TM2GuardAllStep.second_isPolyTime
  have ho : IsPolyTime offset := TM2Compose.isPolyTime_comp tokens guardCount ht guardCount_isPolyTime
  have hz : IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have hf : IsPolyTime first := TM2Compose.isPolyTime_comp (fun p : Input => (original p,zero p))
    Source284RowNormalizationTM2.lookupPair (TM2GuardAllStep.pair_isPolyTime original zero hr hz)
    Source284RowNormalizationTM2.lookupPair_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p : Input => (offset p,first p)) shiftPair
    (TM2GuardAllStep.pair_isPolyTime offset first ho hf) shiftPair_isPolyTime

def atHandoff (p : Request) : Bool :=
  !TM2BoundedWitnessGuard.numericNe (p.2,handoff p.1.1)

theorem atHandoff_isPolyTime : IsPolyTime atHandoff := by
  let data : Request → Input := fun p => p.1
  let index : Request → Nat := fun p => p.2
  let tokens : Request → List Bool := fun p => (data p).1
  let target : Request → Nat := fun p => handoff (tokens p)
  have hd : IsPolyTime data := TM2PairFirst.first_isPolyTime
  have hi : IsPolyTime index := TM2GuardAllStep.second_isPolyTime
  have ht : IsPolyTime tokens := TM2Compose.isPolyTime_comp data (fun p : Input => p.1)
    hd TM2PairFirst.first_isPolyTime
  have hh : IsPolyTime target := TM2Compose.isPolyTime_comp tokens handoff ht handoff_isPolyTime
  have hn := TM2Compose.isPolyTime_comp (fun p : Request => (index p,target p))
    TM2BoundedWitnessGuard.numericNe (TM2GuardAllStep.pair_isPolyTime index target hi hh)
    TM2BoundedWitnessGuard.numericNe_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p : Request => TM2BoundedWitnessGuard.numericNe (p.2,handoff p.1.1))
    Bool.not hn TM2GateDispatch.not_isPolyTime

def guardPair (p : Request) : EncRow × EncRow :=
  if atHandoff p then firstShift p.1 else Source284FixedGuardRowsTM2.rowPair (p.1.1,p.2)

theorem guardPair_isPolyTime : IsPolyTime guardPair := by
  let data : Request → Input := fun p => p.1
  let index : Request → Nat := fun p => p.2
  let tokens : Request → List Bool := fun p => (data p).1
  have hd : IsPolyTime data := TM2PairFirst.first_isPolyTime
  have hi : IsPolyTime index := TM2GuardAllStep.second_isPolyTime
  have ht : IsPolyTime tokens := TM2Compose.isPolyTime_comp data (fun p : Input => p.1)
    hd TM2PairFirst.first_isPolyTime
  have hf : IsPolyTime (fun p : Request => firstShift (data p)) :=
    TM2Compose.isPolyTime_comp data firstShift hd firstShift_isPolyTime
  have hg : IsPolyTime (fun p : Request => Source284FixedGuardRowsTM2.rowPair (tokens p,index p)) :=
    TM2Compose.isPolyTime_comp (fun p : Request => (tokens p,index p))
      Source284FixedGuardRowsTM2.rowPair (TM2GuardAllStep.pair_isPolyTime tokens index ht hi)
      Source284FixedGuardRowsTM2.rowPair_isPolyTime
  exact TM2If.if_isPolyTime atHandoff (fun p => firstShift (data p))
    (fun p => Source284FixedGuardRowsTM2.rowPair (tokens p,index p)) atHandoff_isPolyTime hf hg

def guardPrefix (p : Input) : EncRows :=
  TM2ContextMapGeneric.contextMap guardPair
    (p,TM2UnaryRange.rangeFromTokens (Source284FixedGuardRowsTM2.stateTokens p.1))

def relocated (p : Input) : EncRows :=
  TM2ContextMapGeneric.contextMap shiftPair (guardCount p.1,p.2)

def rows (p : Input) : EncRows := guardPrefix p ++ relocated p

theorem rows_isPolyTime : IsPolyTime rows := by
  let tokens : Input → List Bool := fun p => p.1
  let original : Input → EncRows := fun p => p.2
  let offset : Input → Nat := fun p => guardCount (tokens p)
  let indices : Input → List Nat := fun p => TM2UnaryRange.rangeFromTokens
    (Source284FixedGuardRowsTM2.stateTokens (tokens p))
  let guarded : Input → EncRows := guardPrefix
  let shifted : Input → EncRows := relocated
  have hi : IsPolyTime (id : Input → Input) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have ht : IsPolyTime tokens := TM2PairFirst.first_isPolyTime
  have hr : IsPolyTime original := TM2GuardAllStep.second_isPolyTime
  have ho : IsPolyTime offset := TM2Compose.isPolyTime_comp tokens guardCount ht guardCount_isPolyTime
  have hs : IsPolyTime (fun p : Input => Source284FixedGuardRowsTM2.stateTokens (tokens p)) :=
    TM2Compose.isPolyTime_comp tokens Source284FixedGuardRowsTM2.stateTokens ht
      Source284FixedGuardRowsTM2.stateTokens_isPolyTime
  have hn : IsPolyTime indices := TM2Compose.isPolyTime_comp
    (fun p : Input => Source284FixedGuardRowsTM2.stateTokens (tokens p))
    TM2UnaryRange.rangeFromTokens hs TM2UnaryRange.rangeFromTokens_isPolyTime
  have hp : IsPolyTime guarded := TM2Compose.isPolyTime_comp (fun p : Input => (id p,indices p))
    (TM2ContextMapGeneric.contextMap guardPair) (TM2GuardAllStep.pair_isPolyTime id indices hi hn)
    (TM2ContextMapGeneric.contextMap_isPolyTime guardPair guardPair_isPolyTime)
  have hg : IsPolyTime shifted := TM2Compose.isPolyTime_comp (fun p : Input => (offset p,original p))
    (TM2ContextMapGeneric.contextMap shiftPair) (TM2GuardAllStep.pair_isPolyTime offset original ho hr)
    (TM2ContextMapGeneric.contextMap_isPolyTime shiftPair shiftPair_isPolyTime)
  exact TM2Compose.isPolyTime_comp (fun p : Input => (guarded p,shifted p))
    (TM2ListAppend.append (α := EncRow × EncRow)) (TM2GuardAllStep.pair_isPolyTime guarded shifted hp hg)
    TM2ListAppend.append_isPolyTime

theorem guardPrefix_length (p : Input) : (guardPrefix p).length = guardCount p.1 := by
  simp [guardPrefix,TM2ContextMapGeneric.contextMap,TM2UnaryRange.rangeFromTokens,guardCount]

theorem relocated_length (p : Input) : (relocated p).length = p.2.length := by
  simp [relocated,TM2ContextMapGeneric.contextMap]

theorem rows_length (p : Input) :
    (rows p).length = Source284FixedGuardRewind.states p.1.length+p.2.length := by
  simp [rows,guardPrefix_length,relocated_length,guardCount_eq]

/-- The handoff row takes the original verifier's actual first row, with its
successor relocated into the appended verifier block. -/
theorem firstShift_correct (p : Input) (b : Bool) :
    decodeRow (if b then (firstShift p).2 else (firstShift p).1) =
      Source284HardwireTable.shiftRow (guardCount p.1)
        (Source284ListTables.table (decodeRows p.2) 0 b) := by
  have h := Source284RowNormalizationTM2.lookupPair_correct p.2 0 b
  cases b <;>
    simp only [Bool.false_eq_true,Bool.true_eq_false,↓reduceIte] at h ⊢ <;>
    simp [firstShift,shiftPair,Source284HardwireEncodedWorkersTM2.decode_shiftEncoded,h]

theorem atHandoff_correct (p : Request) :
    atHandoff p = decide (p.2 = Source284FixedGuardRewind.handoff p.1.1.length) := by
  by_cases h : p.2 = Source284FixedGuardRewind.handoff p.1.1.length <;>
    simp [atHandoff,handoff_eq,TM2BoundedWitnessGuard.numericNe,h]

/-- The generated prefix agrees with the linked table at each guard state. -/
theorem guardPair_correct (p : Input) (q : Nat)
    (hq : q < Source284FixedGuardRewind.states p.1.length) (b : Bool) :
    decodeRow (if b then (guardPair (p,q)).2 else (guardPair (p,q)).1) =
      Source284FixedGuardLink.table p.1.length (Source284ListTables.table (decodeRows p.2)) q b := by
  by_cases hh : q = Source284FixedGuardRewind.handoff p.1.length
  · have ha : atHandoff (p,q) = true := by simp [atHandoff_correct,hh]
    have hf := firstShift_correct p b
    simp only [guardPair,ha,↓reduceIte] at *
    rw [hf]
    simp [Source284FixedGuardLink.table,hh,guardCount_eq]
  · have ha : atHandoff (p,q) = false := by simp [atHandoff_correct,hh]
    have hf := Source284FixedGuardRowTM2.row_correct p.1 q b
    simp only [guardPair,ha,Bool.false_eq_true,↓reduceIte,Source284FixedGuardRowsTM2.rowPair] at *
    rw [Source284FixedGuardLink.guard_row p.1.length _ q b hq hh]
    cases b <;> simpa using hf

theorem guardPrefix_correct (p : Input) (q : Nat)
    (hq : q < Source284FixedGuardRewind.states p.1.length) (b : Bool) :
    decodeRow (if b then ((guardPrefix p)[q]?).getD Source284RowNormalizationTM2.fallback |>.2
      else ((guardPrefix p)[q]?).getD Source284RowNormalizationTM2.fallback |>.1) =
      Source284FixedGuardLink.table p.1.length (Source284ListTables.table (decodeRows p.2)) q b := by
  have hh := guardPair_correct p q hq b
  simpa [guardPrefix,TM2ContextMapGeneric.contextMap,TM2UnaryRange.rangeFromTokens,
    Source284FixedGuardRowsTM2.stateTokens_length,hq] using hh

theorem relocated_correct (p : Input) (q : Nat) (hq : q < p.2.length) (b : Bool) :
    decodeRow (if b then ((relocated p)[q]?).getD Source284RowNormalizationTM2.fallback |>.2
      else ((relocated p)[q]?).getD Source284RowNormalizationTM2.fallback |>.1) =
      Source284HardwireTable.shiftRow (guardCount p.1)
        (Source284ListTables.table (decodeRows p.2) q b) := by
  have hh := Source284EncodedRows.lookup p.2 q hq b
  cases b <;> simp [relocated,TM2ContextMapGeneric.contextMap,
    List.getElem?_eq_getElem hq,shiftPair,Source284HardwireEncodedWorkersTM2.decode_shiftEncoded] at hh ⊢ <;>
    rw [← hh]

/-- Every generated linked row decodes to the previously verified handoff
composition. This also covers arbitrary malformed verifier row lists. -/
theorem rows_correct (p : Input) (q : Nat)
    (hq : q < Source284FixedGuardRewind.states p.1.length+p.2.length) (b : Bool) :
    Source284ListTables.table (decodeRows (rows p)) q b =
      Source284FixedGuardLink.table p.1.length (Source284ListTables.table (decodeRows p.2)) q b := by
  have hq' : q < (rows p).length := by simpa [rows_length] using hq
  rw [Source284EncodedRows.lookup _ q hq' b]
  by_cases hg : q < Source284FixedGuardRewind.states p.1.length
  · have hp : q < (guardPrefix p).length := by simpa [guardPrefix_length,guardCount_eq] using hg
    have helem : (rows p)[q] = (guardPrefix p)[q] := by
      simpa only [rows] using (List.getElem_append_left (as := guardPrefix p) (bs := relocated p) hp)
    rw [helem]
    have h := guardPrefix_correct p q hg b
    simpa [List.getElem?_eq_getElem hp] using h
  · have hp : (guardPrefix p).length ≤ q := by simp [guardPrefix_length,guardCount_eq]; omega
    have hqrel : q-(guardPrefix p).length < p.2.length := by
      simp only [guardPrefix_length,guardCount_eq] at *
      omega
    have hrelLen : q-(guardPrefix p).length < (relocated p).length := by
      simpa [relocated_length] using hqrel
    have helem : (rows p)[q] = (relocated p)[q-(guardPrefix p).length] := by
      simpa only [rows] using (List.getElem_append_right (as := guardPrefix p) (bs := relocated p) hp)
    rw [helem]
    have h := relocated_correct p (q-(guardPrefix p).length) hqrel b
    simp only [List.getElem?_eq_getElem hrelLen,Option.getD_some] at h
    rw [h]
    simp only [guardPrefix_length,guardCount_eq]
    have heq : q = Source284FixedGuardRewind.states p.1.length+
        (q-Source284FixedGuardRewind.states p.1.length) := by omega
    conv_rhs => rw [heq]
    rw [Source284FixedGuardLink.relocated_row]

/-- A closed, nonempty verifier yields an executable validity check for the
entire linked output table. -/
theorem rows_valid (p : Input) (hne : 0 < p.2.length)
    (hv : Source284ListTables.valid (decodeRows p.2) = true) :
    Source284ListTables.valid (decodeRows (rows p)) = true := by
  apply Source284EmptyBranchValidity.valid_of_closed
  intro q hq b q' hn
  have hq' : q < Source284FixedGuardRewind.states p.1.length+p.2.length := by
    simpa [rows_length] using hq
  rw [rows_correct p q hq' b] at hn
  have hclosed : Closed p.2.length (Source284ListTables.table (decodeRows p.2)) := by
    simpa using Source284ListTables.valid_closed (decodeRows p.2) hv
  have h := Source284FixedGuardLink.closed p.1.length p.2.length _ hne hclosed q hq' b q' hn
  simpa [rows_length] using h

end Shared.Beeping.NPcoNP.Source284FixedGuardLinkedRowsTM2
