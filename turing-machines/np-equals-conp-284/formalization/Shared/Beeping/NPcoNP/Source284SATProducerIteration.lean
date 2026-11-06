import Shared.Beeping.NPcoNP.Source284SATProducerSize
import Shared.ComplexityBridge.TM2ListUnaryLength
import Shared.ComplexityBridge.TM2UnaryRange
import Shared.ComplexityBridge.TM2ContextMapGeneric

/-! Constructing the complete table reduces to evaluating its individual
rows and traversing a unary-sized range. The remaining row-worker cost is an
explicit premise; no polynomial-time claim is made for it here. -/
namespace Shared.Beeping.NPcoNP.Source284SATProducerIteration

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284SATTableParameters

abbrev Input := List Bool × (List Bool × EncRows)

def budget (p : Input) : List Bool :=
  p.1 ++ p.1 ++ p.2.1 ++ p.2.1 ++ p.2.1 ++ p.2.1 ++ p.2.1 ++ p.2.1 ++
    TM2ListUnaryLength.unaryLength p.2.2 ++ List.replicate 9 true

theorem budget_length (p : Input) : (budget p).length = (produceRows p).length := by
  simp [budget,TM2ListUnaryLength.unaryLength,Source284SATProducerSize.rows_length]
  omega

private theorem append_poly {α : Type} [BitstringEncoding α]
    (f g : α → List Bool) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun p => f p ++ g p) := by
  have h := TM2GuardAllStep.pair_isPolyTime f g hf hg
  simpa [TM2ListAppend.append] using TM2Compose.isPolyTime_comp (fun p => (f p,g p))
    (TM2ListAppend.append (α := Bool)) h TM2ListAppend.append_isPolyTime

theorem budget_isPolyTime : IsPolyTime budget := by
  let first : Input → List Bool := fun p => p.1
  let second : Input → List Bool × EncRows := fun p => p.2
  let ticks : Input → List Bool := fun p => (second p).1
  let original : Input → EncRows := fun p => (second p).2
  let rows : Input → List Bool := fun p => TM2ListUnaryLength.unaryLength (original p)
  let nine : Input → List Bool := fun p => TM2UnaryPolynomialIO.unaryPolynomial (Polynomial.C 9) (first p)
  have hf : IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hs : IsPolyTime second := TM2GuardAllStep.second_isPolyTime
  have ht : IsPolyTime ticks := TM2Compose.isPolyTime_comp second (fun p : List Bool × EncRows => p.1)
    hs TM2PairFirst.first_isPolyTime
  have ho : IsPolyTime original := TM2Compose.isPolyTime_comp second (fun p : List Bool × EncRows => p.2)
    hs TM2GuardAllStep.second_isPolyTime
  have hr : IsPolyTime rows := TM2Compose.isPolyTime_comp original
    TM2ListUnaryLength.unaryLength ho TM2ListUnaryLength.unaryLength_isPolyTime
  have hn : IsPolyTime nine := TM2Compose.isPolyTime_comp first
    (TM2UnaryPolynomialIO.unaryPolynomial (Polynomial.C 9)) hf
    (TM2UnaryPolynomialIO.unaryPolynomial_isPolyTime (Polynomial.C 9))
  have h1 := append_poly rows nine hr hn
  have h2 := append_poly ticks (fun p => rows p ++ nine p) ht h1
  have h3 := append_poly ticks (fun p => ticks p ++ (rows p ++ nine p)) ht h2
  have h4 := append_poly ticks (fun p => ticks p ++ (ticks p ++ (rows p ++ nine p))) ht h3
  have h5 := append_poly ticks (fun p => ticks p ++ (ticks p ++ (ticks p ++ (rows p ++ nine p)))) ht h4
  have h6 := append_poly ticks (fun p => ticks p ++ (ticks p ++ (ticks p ++ (ticks p ++ (rows p ++ nine p))))) ht h5
  have h7 := append_poly ticks (fun p => ticks p ++ (ticks p ++ (ticks p ++ (ticks p ++ (ticks p ++ (rows p ++ nine p)))))) ht h6
  have h8 := append_poly first (fun p => ticks p ++ (ticks p ++ (ticks p ++ (ticks p ++ (ticks p ++ (ticks p ++ (rows p ++ nine p))))))) hf h7
  have h := append_poly first _ hf h8
  change IsPolyTime (fun p : Input => budget p)
  simpa [budget,first,second,ticks,original,rows,nine,TM2UnaryPolynomialIO.unaryPolynomial,
    Polynomial.eval_C,List.append_assoc] using h

/-- The worker computes exactly one encoded transition pair. -/
def rowWorker (request : Input × Nat) : EncRow × EncRow :=
  let p := request.1
  let q := request.2
  let expected := p.1
  let clock := p.2.1.length
  let original := Source284ListTables.table (decodeRows p.2.2)
  let validator := Source284VerifierHandoff.table expected clock original
  let t := Source284FacingAdapter.table validator
  (encodeRow (t q false),encodeRow (t q true))

def iterated (p : Input) : EncRows :=
  TM2ContextMapGeneric.contextMap rowWorker (p,TM2UnaryRange.rangeFromTokens (budget p))

theorem iterated_eq (p : Input) : iterated p = produceRows p := by
  have hlen : (budget p).length = (produceRows p).length := budget_length p
  unfold iterated TM2ContextMapGeneric.contextMap TM2UnaryRange.rangeFromTokens
  rw [hlen]
  unfold produceRows Source284MaterializeRows.rows encodeRows
  simp only [List.map_map, Function.comp_def, List.ofFn_eq_map]
  simp only [rowWorker, ← List.map_coe_finRange_eq_range, List.map_map, Function.comp_def]
  rw [List.length_map, List.length_finRange]

theorem produceRows_isPolyTime_of_worker (hworker : IsPolyTime rowWorker) :
    IsPolyTime produceRows := by
  let indices : Input → List Nat := fun p => TM2UnaryRange.rangeFromTokens (budget p)
  have hi : IsPolyTime (id : Input → Input) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hr : IsPolyTime indices := TM2Compose.isPolyTime_comp budget TM2UnaryRange.rangeFromTokens
    budget_isPolyTime TM2UnaryRange.rangeFromTokens_isPolyTime
  have ha := TM2GuardAllStep.pair_isPolyTime (id : Input → Input) indices hi hr
  have hm := TM2Compose.isPolyTime_comp (fun p : Input => (p,indices p))
    (TM2ContextMapGeneric.contextMap rowWorker) ha
    (TM2ContextMapGeneric.contextMap_isPolyTime rowWorker hworker)
  have he : iterated = produceRows := by funext p; exact iterated_eq p
  rw [← he]
  exact hm

/-- The traversal never requests an index outside its explicit unary budget.
The bounded worker supplies a fixed default for all other binary inputs, so
its future cost proof need not execute an unbounded-index branch. -/
def boundedRowWorker (request : Input × Nat) : EncRow × EncRow :=
  if request.2 < (budget request.1).length then rowWorker request
  else ((false,false,false,0),(false,false,false,0))

theorem bounded_map_eq (p : Input) :
    TM2ContextMapGeneric.contextMap boundedRowWorker
      (p,TM2UnaryRange.rangeFromTokens (budget p)) = produceRows p := by
  rw [← iterated_eq p]
  simp only [iterated,TM2ContextMapGeneric.contextMap,TM2UnaryRange.rangeFromTokens]
  apply List.map_congr_left
  intro q hq
  have hbound : q < (budget p).length := by simpa using hq
  simp [boundedRowWorker,hbound]

theorem produceRows_isPolyTime_of_bounded_worker (hworker : IsPolyTime boundedRowWorker) :
    IsPolyTime produceRows := by
  let indices : Input → List Nat := fun p => TM2UnaryRange.rangeFromTokens (budget p)
  have hi : IsPolyTime (id : Input → Input) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hr : IsPolyTime indices := TM2Compose.isPolyTime_comp budget TM2UnaryRange.rangeFromTokens
    budget_isPolyTime TM2UnaryRange.rangeFromTokens_isPolyTime
  have ha := TM2GuardAllStep.pair_isPolyTime (id : Input → Input) indices hi hr
  have hm := TM2Compose.isPolyTime_comp (fun p : Input => (p,indices p))
    (TM2ContextMapGeneric.contextMap boundedRowWorker) ha
    (TM2ContextMapGeneric.contextMap_isPolyTime boundedRowWorker hworker)
  have he : (fun p : Input => TM2ContextMapGeneric.contextMap boundedRowWorker (p,indices p)) =
      produceRows := by funext p; exact bounded_map_eq p
  rw [← he]
  exact hm

end Shared.Beeping.NPcoNP.Source284SATProducerIteration
