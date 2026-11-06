import Shared.Beeping.NPcoNP.Source284CountdownSearch
import Shared.ComplexityBridge.TM2UnaryRange
import Shared.ComplexityBridge.TM2FlattenList

/-! Canonical polynomial-time generation of a finite countdown rectangle.
Both dimensions are supplied in unary: the list contents are ignored and
only their lengths matter. Generating a rectangle of binary-sized dimensions
without charging for its output would not satisfy this theorem. -/
namespace Shared.Beeping.NPcoNP.Source284RectangleTM2

open Shared.ComplexityBridge

/-- All original-state coordinates for one elapsed coordinate. -/
def row (p : List Bool × Nat) : List (Nat × Nat) :=
  TM2ContextMapGeneric.contextMap id (p.2, TM2UnaryRange.rangeFromTokens p.1)

theorem row_isPolyTime : ComplexityTheory.IsPolyTime row := by
  let tokens : List Bool × Nat → List Bool := fun p => p.1
  let elapsed : List Bool × Nat → Nat := fun p => p.2
  let indices : List Bool × Nat → List Nat := fun p => TM2UnaryRange.rangeFromTokens (tokens p)
  let args : List Bool × Nat → Nat × List Nat := fun p => (elapsed p, indices p)
  have ht : ComplexityTheory.IsPolyTime tokens := TM2PairFirst.first_isPolyTime
  have he : ComplexityTheory.IsPolyTime elapsed := TM2GuardAllStep.second_isPolyTime
  have hi : ComplexityTheory.IsPolyTime indices :=
    TM2Compose.isPolyTime_comp tokens TM2UnaryRange.rangeFromTokens ht TM2UnaryRange.rangeFromTokens_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime elapsed indices he hi
  have hid : ComplexityTheory.IsPolyTime (id : Nat × Nat → Nat × Nat) :=
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have h := TM2Compose.isPolyTime_comp args (TM2ContextMapGeneric.contextMap id) ha
    (TM2ContextMapGeneric.contextMap_isPolyTime (id : Nat × Nat → Nat × Nat) hid)
  exact h

/-- Enumerate elapsed coordinates first, then original state coordinates. -/
def generate (p : List Bool × List Bool) : List (Nat × Nat) :=
  (TM2ContextMapGeneric.contextMap row
    (p.1, TM2UnaryRange.rangeFromTokens p.2)).flatten

theorem generate_isPolyTime : ComplexityTheory.IsPolyTime generate := by
  let tokens : List Bool × List Bool → List Bool := fun p => p.1
  let elapsedTokens : List Bool × List Bool → List Bool := fun p => p.2
  let indices : List Bool × List Bool → List Nat := fun p => TM2UnaryRange.rangeFromTokens (elapsedTokens p)
  let args : List Bool × List Bool → List Bool × List Nat := fun p => (tokens p, indices p)
  let blocks : List Bool × List Bool → List (List (Nat × Nat)) :=
    fun p => TM2ContextMapGeneric.contextMap row (args p)
  have ht : ComplexityTheory.IsPolyTime tokens := TM2PairFirst.first_isPolyTime
  have he : ComplexityTheory.IsPolyTime elapsedTokens := TM2GuardAllStep.second_isPolyTime
  have hi : ComplexityTheory.IsPolyTime indices :=
    TM2Compose.isPolyTime_comp elapsedTokens TM2UnaryRange.rangeFromTokens he TM2UnaryRange.rangeFromTokens_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime tokens indices ht hi
  have hb : ComplexityTheory.IsPolyTime blocks :=
    TM2Compose.isPolyTime_comp args (TM2ContextMapGeneric.contextMap row) ha
      (TM2ContextMapGeneric.contextMap_isPolyTime row row_isPolyTime)
  have h := TM2Compose.isPolyTime_comp blocks (List.flatten : List (List (Nat × Nat)) → List (Nat × Nat))
    hb TM2FlattenList.flatten_isPolyTime
  exact h

theorem generate_correct (nTokens elapsedTokens : List Bool) :
    generate (nTokens, elapsedTokens) =
      Source284CountdownSearch.rectangle nTokens.length elapsedTokens.length := by
  simp [generate, row, TM2ContextMapGeneric.contextMap, TM2UnaryRange.rangeFromTokens,
    Source284CountdownSearch.rectangle, List.flatMap]

end Shared.Beeping.NPcoNP.Source284RectangleTM2
