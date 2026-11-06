import Shared.Beeping.NPcoNP.Source284FixedGuardRowTM2
import Shared.Beeping.NPcoNP.Source284EmptyBranchValidity
import Shared.Beeping.NPcoNP.Source284EncodedRecordListTM2
import Shared.Beeping.NPcoNP.Source284TableRowsTM2

/-! A single canonical polynomial-time TM2 constructs the complete fixed
witness-guard table from its unary limit and serializes it to source bits.
This is not an input-dependent verifier, whole-verifier compiler, or literal
284-state machine refinement. -/
namespace Shared.Beeping.NPcoNP.Source284FixedGuardRowsTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284FixedGuardRowTM2
open Shared.Codes.BitNumeralCompare (value)

def stateTokens (tokens : List Bool) : List Bool := endTokens tokens ++ [true]

theorem stateTokens_length (tokens : List Bool) :
    (stateTokens tokens).length = Source284FixedGuardRewind.states tokens.length := by
  simp [stateTokens,endTokens_length,Source284FixedGuardRewind.states]

theorem stateTokens_isPolyTime : IsPolyTime stateTokens :=
  TM2Compose.isPolyTime_comp endTokens (fun xs : List Bool => xs++[true])
    endTokens_isPolyTime addSingleton_isPolyTime

def rowPair (p : List Bool × Nat) : EncRow × EncRow :=
  (row ((p.1,p.2),false),row ((p.1,p.2),true))

theorem rowPair_isPolyTime : IsPolyTime rowPair := by
  let ident : List Bool × Nat → List Bool × Nat := id
  let no : List Bool × Nat → Bool := fun _ => false
  let yes : List Bool × Nat → Bool := fun _ => true
  have hi : IsPolyTime ident := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hn : IsPolyTime no := TM2Constant.isPolyTime false
  have hy : IsPolyTime yes := TM2Constant.isPolyTime true
  have hno : IsPolyTime (fun p : List Bool × Nat => row (ident p,no p)) :=
    TM2Compose.isPolyTime_comp (fun p : List Bool × Nat => (ident p,no p)) row
      (TM2GuardAllStep.pair_isPolyTime ident no hi hn) row_isPolyTime
  have hyes : IsPolyTime (fun p : List Bool × Nat => row (ident p,yes p)) :=
    TM2Compose.isPolyTime_comp (fun p : List Bool × Nat => (ident p,yes p)) row
      (TM2GuardAllStep.pair_isPolyTime ident yes hi hy) row_isPolyTime
  exact TM2GuardAllStep.pair_isPolyTime _ _ hno hyes

def tableRows (tokens : List Bool) : EncRows :=
  TM2ContextMapGeneric.contextMap rowPair (tokens,TM2UnaryRange.rangeFromTokens (stateTokens tokens))

theorem tableRows_isPolyTime : IsPolyTime tableRows := by
  let ident : List Bool → List Bool := id
  let indices : List Bool → List Nat := fun xs => TM2UnaryRange.rangeFromTokens (stateTokens xs)
  have hi : IsPolyTime ident := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hn : IsPolyTime indices := TM2Compose.isPolyTime_comp stateTokens TM2UnaryRange.rangeFromTokens
    stateTokens_isPolyTime TM2UnaryRange.rangeFromTokens_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun xs : List Bool => (ident xs,indices xs))
    (TM2ContextMapGeneric.contextMap rowPair) (TM2GuardAllStep.pair_isPolyTime ident indices hi hn)
    (TM2ContextMapGeneric.contextMap_isPolyTime rowPair rowPair_isPolyTime)

theorem tableRows_length (tokens : List Bool) :
    (tableRows tokens).length = Source284FixedGuardRewind.states tokens.length := by
  simp [tableRows,TM2ContextMapGeneric.contextMap,TM2UnaryRange.rangeFromTokens,stateTokens_length]

/-- Every allocated row, for either symbol, decodes to the actual finite
guard transition. Inputs outside the unary limit are not silently guessed. -/
theorem tableRows_correct (tokens : List Bool) (q : Nat)
    (hq : q < Source284FixedGuardRewind.states tokens.length) (b : Bool) :
    Source284ListTables.table (decodeRows (tableRows tokens)) q b =
      Source284FixedGuardRewind.table tokens.length q b := by
  have hq' : q < (tableRows tokens).length := by simpa [tableRows_length] using hq
  rw [Source284EncodedRows.lookup _ q hq' b]
  cases b with
  | false =>
    simpa [tableRows,rowPair,TM2ContextMapGeneric.contextMap,TM2UnaryRange.rangeFromTokens,
      hq,stateTokens_length] using (Source284FixedGuardRowTM2.row_correct tokens q false)
  | true =>
    simpa [tableRows,rowPair,TM2ContextMapGeneric.contextMap,TM2UnaryRange.rangeFromTokens,
      hq,stateTokens_length] using (Source284FixedGuardRowTM2.row_correct tokens q true)

theorem tableRows_closed (tokens : List Bool) :
    Closed (decodeRows (tableRows tokens)).length (Source284ListTables.table (decodeRows (tableRows tokens))) := by
  intro q hq b q' hn
  have hq' : q < Source284FixedGuardRewind.states tokens.length := by
    simpa [tableRows_length] using hq
  rw [tableRows_correct tokens q hq' b] at hn
  have h := Source284FixedGuardRewind.table_closed tokens.length q hq' b q' hn
  simpa [tableRows_length] using h

theorem tableRows_valid (tokens : List Bool) :
    Source284ListTables.valid (decodeRows (tableRows tokens)) = true :=
  Source284EmptyBranchValidity.valid_of_closed _ (tableRows_closed tokens)

/-- The complete source code is serialized with a charged polynomial-time
serializer, using the real row-list length to bound unary record values. -/
def sourceBits (tokens : List Bool) : List Bool :=
  Source284TableRowsTM2.serializeRows (Source284EncodedRecordList.recordsList (tableRows tokens))

theorem sourceBits_isPolyTime : IsPolyTime sourceBits := by
  have hrecords := TM2Compose.isPolyTime_comp tableRows Source284EncodedRecordList.recordsList
    tableRows_isPolyTime Source284EncodedRecordListTM2.recordsList_isPolyTime
  exact TM2Compose.isPolyTime_comp
    (fun xs : List Bool => Source284EncodedRecordList.recordsList (tableRows xs))
    Source284TableRowsTM2.serializeRows hrecords Source284TableRowsTM2.serializeRows_isPolyTime

theorem sourceBits_correct (tokens : List Bool) :
    value (sourceBits tokens) =
      encode (Source284FixedGuardRewind.states tokens.length)
        (Source284FixedGuardRewind.table tokens.length) 0 := by
  rw [sourceBits,Source284EncodedRecordList.recordsList_eq]
  rw [Source284TableRowsTM2.closed_table_correct _ _ (tableRows_closed tokens)]
  have hr : records (Source284FixedGuardRewind.states tokens.length)
      (Source284ListTables.table (decodeRows (tableRows tokens))) =
      records (Source284FixedGuardRewind.states tokens.length)
        (Source284FixedGuardRewind.table tokens.length) := by
    apply List.ext_getElem
    · simp [records]
    · intro j h1 h2
      have hj : j/2 < Source284FixedGuardRewind.states tokens.length := by
        simp only [records,List.length_ofFn] at h2
        omega
      simp only [records,List.getElem_ofFn]
      rw [tableRows_correct tokens (j/2) hj]
  simp only [decodeRows_length,tableRows_length]
  simp [encode,hr]

namespace Fixtures

-- Empty unary bound: initial scan, turning boundary, rewind, handoff and
-- an out-of-range request. These are kernel-reduced finite checks.
example : row (([],0),false) = (false,true,true,11) := by decide +kernel
example : row (([],28),false) = (false,true,true,30) := by decide +kernel
example : row (([],30),true) = (true,false,true,31) := by decide +kernel
example : row (([],33),false) = (false,false,true,29) := by decide +kernel
example : row (([],40),true) = (true,false,true,29) := by decide +kernel

end Fixtures

end Shared.Beeping.NPcoNP.Source284FixedGuardRowsTM2
