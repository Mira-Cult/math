import Shared.Beeping.NPcoNP.Source284GuardRowCorrect
import Shared.Beeping.NPcoNP.Source284GuardRowPolyTM2
import Shared.ComplexityBridge.TM2UnaryProductLength
import Shared.ComplexityBridge.TM2UnaryRange

/-! Uniform finite countdown-table construction. Its input consists of an
explicit canonically encoded row list and a unary cutoff. Every allocated
state, including unreachable holes and the reject sink, has two explicitly
computed rows. This is not a construction from a function-valued table or a
claim about a binary cutoff. -/
namespace Shared.Beeping.NPcoNP.Source284GuardTableListTM2

open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284GuardRow
open Shared.Beeping.NPcoNP.Source284GuardRowCorrect
open Shared.Beeping.NPcoNP.Source284TableCountdown

abbrev Input := List Bool × EncRows

/-- One extra token beyond the sum of the two numeric bounds. -/
def side (p : Input) : List Bool := budget p.1 p.2 ++ [true]

def square (p : Input) : List Bool := TM2UnaryProductLength.productBits (side p,side p)

/-- A safe square-sized expansion budget is used only to build the exact
number `sink + 1` of state tokens; surplus tokens are not output rows. -/
def stateTokens (p : Input) : List Bool :=
  TM2BoundedUnary.expand (square p ++ [true], sinkCode p.1 p.2) ++ [true]

theorem sink_fits (cutoff : List Bool) (rows : EncRows) :
    sinkCode cutoff rows ≤ (square (cutoff,rows) ++ [true]).length := by
  have ha := allocated_le rows.length cutoff.length
  have hm : max rows.length cutoff.length + 1 ≤ (side (cutoff,rows)).length := by
    simp [side, budget]
    omega
  have hs := Nat.pow_le_pow_left hm 2
  rw [sinkCode_correct]
  simp only [square, List.length_append, List.length_cons, List.length_nil,
    Nat.add_zero, TM2UnaryProductLength.productBits_length]
  simp only [allocated] at ha
  nlinarith [hs]

/-- Exactly one token per allocated state, including the sink. -/
theorem stateTokens_length (cutoff : List Bool) (rows : EncRows) :
    (stateTokens (cutoff,rows)).length = allocated rows.length cutoff.length := by
  have hf := sink_fits cutoff rows
  have hf' : Source284TableCountdown.sink rows.length cutoff.length ≤
      (square (cutoff,rows)).length + 1 := by
    simpa [sinkCode_correct] using hf
  simp [stateTokens, TM2BoundedUnary.expand_correct, sinkCode_correct, allocated,
    Nat.min_eq_left hf']

/-- Both read-symbol rows are computed for each state. -/
def rowPair (p : Input × Nat) : EncRow × EncRow :=
  (guardedRow (p.1,(p.2,false)), guardedRow (p.1,(p.2,true)))

def tableRows (p : Input) : EncRows :=
  TM2ContextMapGeneric.contextMap rowPair
    (p, TM2UnaryRange.rangeFromTokens (stateTokens p))

theorem tableRows_length (cutoff : List Bool) (rows : EncRows) :
    (tableRows (cutoff,rows)).length = allocated rows.length cutoff.length := by
  simp [tableRows, TM2ContextMapGeneric.contextMap, TM2UnaryRange.rangeFromTokens,
    stateTokens_length]

/-- Every allocated row, including an unreachable hole, agrees with the
original countdown table after decoding. The original table is the total
finite-data table induced by the input rows. -/
theorem tableRows_correct (cutoff : List Bool) (rows : EncRows) (q : Nat)
    (hq : q < allocated rows.length cutoff.length) (read : Bool) :
    Source284ListTables.table (decodeRows (tableRows (cutoff,rows))) q read =
      Source284TableCountdown.table rows.length cutoff.length
        (Source284ListTables.table (decodeRows rows)) q read := by
  have hq' : q < (tableRows (cutoff,rows)).length := by
    simpa [tableRows_length] using hq
  rw [Source284EncodedRows.lookup _ q hq' read]
  cases read with
  | false =>
    simpa [tableRows, rowPair, TM2ContextMapGeneric.contextMap,
      TM2UnaryRange.rangeFromTokens, hq, stateTokens_length] using
      (guardedRow_correct cutoff rows q false)
  | true =>
    simpa [tableRows, rowPair, TM2ContextMapGeneric.contextMap,
      TM2UnaryRange.rangeFromTokens, hq, stateTokens_length] using
      (guardedRow_correct cutoff rows q true)

private theorem cutoff_poly : ComplexityTheory.IsPolyTime (fun p : Input => p.1) :=
  TM2PairFirst.first_isPolyTime
private theorem rows_poly : ComplexityTheory.IsPolyTime (fun p : Input => p.2) :=
  TM2GuardAllStep.second_isPolyTime
private theorem one_poly : ComplexityTheory.IsPolyTime (fun _ : Input => [true]) :=
  TM2GateCNFPieces.singleton_isPolyTime (fun _ : Input => true) (TM2Constant.isPolyTime true)
private theorem tokens_poly : ComplexityTheory.IsPolyTime (fun p : Input => nTokens p.2) :=
  TM2Compose.isPolyTime_comp (fun p : Input => p.2) nTokens rows_poly TM2ListUnaryLength.unaryLength_isPolyTime
private theorem budget_poly : ComplexityTheory.IsPolyTime (fun p : Input => budget p.1 p.2) :=
  TM2CircuitTemplate.append_isPolyTime _ _ cutoff_poly tokens_poly
private theorem side_poly : ComplexityTheory.IsPolyTime side :=
  TM2CircuitTemplate.append_isPolyTime _ _ budget_poly one_poly
private theorem square_poly : ComplexityTheory.IsPolyTime square :=
  TM2Compose.isPolyTime_comp (fun p : Input => (side p,side p)) TM2UnaryProductLength.productBits
    (TM2GuardAllStep.pair_isPolyTime side side side_poly side_poly) TM2UnaryProductLength.productBits_isPolyTime
private theorem sink_poly : ComplexityTheory.IsPolyTime (fun p : Input => sinkCode p.1 p.2) := by
  have h := TM2Compose.isPolyTime_comp (fun p : Input => (p.1,nTokens p.2))
    Source284GuardRowCoreTM2.sink (TM2GuardAllStep.pair_isPolyTime _ _ cutoff_poly tokens_poly)
    Source284GuardRowCoreTM2.sink_isPolyTime
  simpa [Source284GuardRowCoreTM2.sink, sinkCode, budget] using h

theorem stateTokens_isPolyTime : ComplexityTheory.IsPolyTime stateTokens := by
  have hb : ComplexityTheory.IsPolyTime (fun p : Input => square p ++ [true]) :=
    TM2CircuitTemplate.append_isPolyTime square (fun _ => [true]) square_poly one_poly
  have he := TM2Compose.isPolyTime_comp (fun p : Input => (square p ++ [true],sinkCode p.1 p.2))
    TM2BoundedUnary.expand (TM2GuardAllStep.pair_isPolyTime _ _ hb sink_poly) TM2BoundedUnary.expand_isPolyTime
  exact TM2CircuitTemplate.append_isPolyTime _ _ he one_poly

theorem rowPair_isPolyTime : ComplexityTheory.IsPolyTime rowPair := by
  let ctx : Input × Nat → Input := fun p => p.1
  let idx : Input × Nat → Nat := fun p => p.2
  have hc : ComplexityTheory.IsPolyTime ctx := TM2PairFirst.first_isPolyTime
  have hi : ComplexityTheory.IsPolyTime idx := TM2GuardAllStep.second_isPolyTime
  have hf : ComplexityTheory.IsPolyTime (fun _ : Input × Nat => false) := TM2Constant.isPolyTime false
  have ht : ComplexityTheory.IsPolyTime (fun _ : Input × Nat => true) := TM2Constant.isPolyTime true
  have ha : ComplexityTheory.IsPolyTime (fun p : Input × Nat => (ctx p,(idx p,false))) :=
    TM2GuardAllStep.pair_isPolyTime ctx (fun p => (idx p,false)) hc (TM2GuardAllStep.pair_isPolyTime idx _ hi hf)
  have hb : ComplexityTheory.IsPolyTime (fun p : Input × Nat => (ctx p,(idx p,true))) :=
    TM2GuardAllStep.pair_isPolyTime ctx (fun p => (idx p,true)) hc (TM2GuardAllStep.pair_isPolyTime idx _ hi ht)
  have h0 := TM2Compose.isPolyTime_comp _ guardedRow ha Source284GuardRowPolyTM2.guardedRow_isPolyTime
  have h1 := TM2Compose.isPolyTime_comp _ guardedRow hb Source284GuardRowPolyTM2.guardedRow_isPolyTime
  exact TM2GuardAllStep.pair_isPolyTime _ _ h0 h1

/-- Canonical polynomial-time construction in the full finite table and
unary cutoff input encodings, including enumeration of all allocated rows. -/
theorem tableRows_isPolyTime : ComplexityTheory.IsPolyTime tableRows := by
  let indices : Input → List Nat := fun p => TM2UnaryRange.rangeFromTokens (stateTokens p)
  have hi : ComplexityTheory.IsPolyTime indices := TM2Compose.isPolyTime_comp stateTokens
    TM2UnaryRange.rangeFromTokens stateTokens_isPolyTime TM2UnaryRange.rangeFromTokens_isPolyTime
  have hid : ComplexityTheory.IsPolyTime (id : Input → Input) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hp := TM2GuardAllStep.pair_isPolyTime id indices hid hi
  exact TM2Compose.isPolyTime_comp (fun p : Input => (p,indices p))
    (TM2ContextMapGeneric.contextMap rowPair) hp
    (TM2ContextMapGeneric.contextMap_isPolyTime rowPair rowPair_isPolyTime)

end Shared.Beeping.NPcoNP.Source284GuardTableListTM2
