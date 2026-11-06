import Shared.Beeping.NPcoNP.Source284FixedGuardLinkedRowsTM2
import Shared.Beeping.NPcoNP.Source284GuardTableListTM2
import Shared.Beeping.NPcoNP.Source284FixedGuardTimedFinite

/-! Canonical polynomial-time construction and serialization of the fixed
witness guard linked to a finite timed verifier. Both the witness limit and
verifier fuel are supplied in unary, and the original verifier is a finite
encoded row list. This does not build an input-dependent source program or
prove the literal 284-state machine refinement. -/
namespace Shared.Beeping.NPcoNP.Source284FixedGuardTimedTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Codes.BitNumeralCompare (value)

abbrev Input := List Bool × (List Bool × EncRows)

def clockTokens (fuel : List Bool) : List Bool := fuel ++ [true]

theorem clockTokens_isPolyTime : IsPolyTime clockTokens :=
  Source284FixedGuardRowTM2.addSingleton_isPolyTime

def timedRows (p : Input) : EncRows :=
  Source284GuardTableListTM2.tableRows (clockTokens p.2.1,p.2.2)

theorem timedRows_isPolyTime : IsPolyTime timedRows := by
  let rest : Input → List Bool × EncRows := fun p => p.2
  let fuel : Input → List Bool := fun p => (rest p).1
  let original : Input → EncRows := fun p => (rest p).2
  let ticks : Input → List Bool := fun p => clockTokens (fuel p)
  have hr : IsPolyTime rest := TM2GuardAllStep.second_isPolyTime
  have hf : IsPolyTime fuel := TM2Compose.isPolyTime_comp rest
    (fun p : List Bool × EncRows => p.1) hr TM2PairFirst.first_isPolyTime
  have ho : IsPolyTime original := TM2Compose.isPolyTime_comp rest
    (fun p : List Bool × EncRows => p.2) hr TM2GuardAllStep.second_isPolyTime
  have ht : IsPolyTime ticks := TM2Compose.isPolyTime_comp fuel clockTokens hf clockTokens_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p : Input => (ticks p,original p))
    Source284GuardTableListTM2.tableRows (TM2GuardAllStep.pair_isPolyTime ticks original ht ho)
    Source284GuardTableListTM2.tableRows_isPolyTime

def rows (p : Input) : EncRows :=
  Source284FixedGuardLinkedRowsTM2.rows (p.1,timedRows p)

theorem rows_isPolyTime : IsPolyTime rows := by
  have hm : IsPolyTime (fun p : Input => p.1) := TM2PairFirst.first_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p : Input => (p.1,timedRows p))
    Source284FixedGuardLinkedRowsTM2.rows
    (TM2GuardAllStep.pair_isPolyTime _ _ hm timedRows_isPolyTime)
    Source284FixedGuardLinkedRowsTM2.rows_isPolyTime

theorem timedRows_length (p : Input) :
    (timedRows p).length = Source284FixedGuardTimed.timedStates p.2.2.length p.2.1.length := by
  simp [timedRows,Source284GuardTableListTM2.tableRows_length,clockTokens,
    Source284FixedGuardTimed.timedStates]

theorem rows_length (p : Input) :
    (rows p).length = Source284FixedGuardTimed.statesTotal p.1.length p.2.2.length p.2.1.length := by
  simp [rows,Source284FixedGuardLinkedRowsTM2.rows_length,timedRows_length,
    Source284FixedGuardTimed.statesTotal]

theorem timedRows_correct (p : Input) (q : Nat) (b : Bool)
    (hq : q < Source284FixedGuardTimed.timedStates p.2.2.length p.2.1.length) :
    Source284ListTables.table (decodeRows (timedRows p)) q b =
      Source284FixedGuardTimed.timed p.2.2.length p.2.1.length
        (Source284ListTables.table (decodeRows p.2.2)) q b := by
  have h := Source284GuardTableListTM2.tableRows_correct (clockTokens p.2.1) p.2.2 q
    (by simpa [clockTokens,Source284FixedGuardTimed.timedStates] using hq) b
  simpa [timedRows,clockTokens,Source284FixedGuardTimed.timed] using h

/-- Every generated transition agrees with the actual timed guard table,
including verifier handoff and every allocated timeout state. -/
theorem rows_correct (p : Input) (q : Nat) (b : Bool)
    (hq : q < Source284FixedGuardTimed.statesTotal p.1.length p.2.2.length p.2.1.length) :
    Source284ListTables.table (decodeRows (rows p)) q b =
      Source284FixedGuardTimed.table p.1.length p.2.2.length p.2.1.length
        (Source284ListTables.table (decodeRows p.2.2)) q b := by
  have hq' : q < Source284FixedGuardRewind.states p.1.length+(timedRows p).length := by
    simpa [timedRows_length,Source284FixedGuardTimed.statesTotal] using hq
  rw [rows,Source284FixedGuardLinkedRowsTM2.rows_correct (p.1,timedRows p) q hq' b]
  change Source284FixedGuardLink.table p.1.length (Source284ListTables.table (decodeRows (timedRows p))) q b = _
  unfold Source284FixedGuardTimed.table
  by_cases hh : q = Source284FixedGuardRewind.handoff p.1.length
  · simp only [Source284FixedGuardLink.table,hh,↓reduceIte]
    have hpos : 0 < Source284FixedGuardTimed.timedStates p.2.2.length p.2.1.length :=
      Source284FixedGuardTimed.timed_positive _ _
    rw [timedRows_correct p 0 b hpos]
  · by_cases hs : Source284FixedGuardRewind.states p.1.length ≤ q
    · have hi : q-Source284FixedGuardRewind.states p.1.length <
          Source284FixedGuardTimed.timedStates p.2.2.length p.2.1.length := by
        unfold Source284FixedGuardTimed.statesTotal at hq
        omega
      simp only [Source284FixedGuardLink.table,hh,hs,↓reduceIte]
      rw [timedRows_correct p _ b hi]
    · simp [Source284FixedGuardLink.table,hh,hs]

theorem rows_closed (p : Input) :
    Closed (decodeRows (rows p)).length (Source284ListTables.table (decodeRows (rows p))) := by
  intro q hq b q' hn
  have hq' : q < Source284FixedGuardTimed.statesTotal p.1.length p.2.2.length p.2.1.length := by
    simpa [rows_length] using hq
  rw [rows_correct p q b hq'] at hn
  have h := Source284FixedGuardTimed.closed p.1.length p.2.2.length p.2.1.length
    (Source284ListTables.table (decodeRows p.2.2)) q hq' b q' hn
  simpa [rows_length] using h

/-- Even malformed supplied verifier rows generate a finite valid guarded
table: the countdown redirects out-of-range successors to its sink. -/
theorem rows_valid (p : Input) : Source284ListTables.valid (decodeRows (rows p)) = true :=
  Source284EmptyBranchValidity.valid_of_closed _ (rows_closed p)

def sourceBits (p : Input) : List Bool :=
  Source284TableRowsTM2.serializeRows (Source284EncodedRecordList.recordsList (rows p))

theorem sourceBits_isPolyTime : IsPolyTime sourceBits := by
  have hrecords := TM2Compose.isPolyTime_comp rows Source284EncodedRecordList.recordsList
    rows_isPolyTime Source284EncodedRecordListTM2.recordsList_isPolyTime
  exact TM2Compose.isPolyTime_comp
    (fun p : Input => Source284EncodedRecordList.recordsList (rows p))
    Source284TableRowsTM2.serializeRows hrecords Source284TableRowsTM2.serializeRows_isPolyTime

/-- The computed bits are exactly the numeric zero-tail source description
of the timed guard, not merely a table with matching sample executions. -/
theorem sourceBits_correct (p : Input) :
    value (sourceBits p) = Source284FixedGuardTimed.description p.1.length p.2.2.length p.2.1.length 0
      (Source284ListTables.table (decodeRows p.2.2)) := by
  rw [sourceBits,Source284EncodedRecordList.recordsList_eq]
  rw [Source284TableRowsTM2.closed_table_correct _ _ (rows_closed p)]
  have hr : records (Source284FixedGuardTimed.statesTotal p.1.length p.2.2.length p.2.1.length)
      (Source284ListTables.table (decodeRows (rows p))) =
      records (Source284FixedGuardTimed.statesTotal p.1.length p.2.2.length p.2.1.length)
        (Source284FixedGuardTimed.table p.1.length p.2.2.length p.2.1.length
          (Source284ListTables.table (decodeRows p.2.2))) := by
    apply List.ext_getElem
    · simp [records]
    · intro j h1 h2
      have hj : j/2 < Source284FixedGuardTimed.statesTotal p.1.length p.2.2.length p.2.1.length := by
        simp only [records,List.length_ofFn] at h2
        omega
      simp only [records,List.getElem_ofFn]
      rw [rows_correct p (j/2) _ hj]
  simp only [decodeRows_length,rows_length,Source284FixedGuardTimed.description]
  simp [encode,hr]

/-- The executable generator produces the same number as the independently
materialized finite table used in the source-execution theorems. -/
theorem sourceBits_eq_source (p : Input) :
    value (sourceBits p) = Source284FixedGuardTimedFinite.source p.1.length p.2.1.length p.2.2 := by
  rw [Source284FixedGuardTimedFinite.source_eq,sourceBits_correct]

/-- The generated program reaches acceptance or a reject sink by the stated
finite clock when the supplied verifier is nonempty and valid. -/
theorem sourceBits_finished (p : Input) (i c : Nat)
    (hn : 0 < p.2.2.length)
    (hv : Source284ListTables.valid (decodeRows p.2.2) = true) :
    let s := (Source284Relative.run (value (sourceBits p))
      (Source284Relative.initial i c) (Source284FixedGuardTimed.time p.1.length p.2.1.length)).state
    s = 0 ∨ s = active (Source284FixedGuardTimed.guardSink p.1.length) ∨
      s = active (Source284FixedGuardTimed.timedSink p.1.length p.2.2.length p.2.1.length) := by
  rw [sourceBits_eq_source]
  exact Source284FixedGuardTimedFinite.source_finished p.1.length p.2.1.length c i p.2.2 hn hv

/-- Given the explicitly supplied verifier-correctness hypothesis, the
actual generated program performs the bounded witness search at every later
clock. This does not provide the input-dependent verifier compiler. -/
theorem sourceBits_coupled_search (p : Input) (i extra : Nat)
    (predicate : List Bool → Bool) (hn : 0 < p.2.2.length)
    (hv : Source284ListTables.valid (decodeRows p.2.2) = true)
    (hmatch : ∀ c w, Source284TaggedWitnessCodec.decode p.1.length c = some w →
      (run (Source284ListTables.table (decodeRows p.2.2)) ⟨c,i,some 0⟩ (p.2.1.length+1)).state.isNone =
        predicate w) :
    Source284Relative.acceptBound (value (sourceBits p)) i
      (Source284FixedGuardTimed.time p.1.length p.2.1.length+extra)
      (2^(Source284FixedGuardTimed.time p.1.length p.2.1.length+extra)) = true ↔
        ∃ w, w.length ≤ p.1.length ∧ predicate w = true := by
  rw [sourceBits_eq_source]
  exact Source284FixedGuardTimedFinite.source_coupled_stable_search
    p.1.length p.2.1.length i extra p.2.2 predicate hn hv hmatch

end Shared.Beeping.NPcoNP.Source284FixedGuardTimedTM2
