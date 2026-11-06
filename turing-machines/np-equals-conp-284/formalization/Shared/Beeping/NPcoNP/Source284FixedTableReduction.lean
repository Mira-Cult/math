import Shared.Beeping.NPcoNP.Source284TableFrame
import Shared.Beeping.NPcoNP.Source284CanonicalConditional

/-! An actual canonical polynomial many-one reduction for each fixed
finite relative table. The varying raw input supplies unary padding, so this
is a tally-style language: its bit values carry no additional machine input.
The result is not SAT hardness and does not construct a uniform table
serializer. -/

namespace Shared.Beeping.NPcoNP.Source284FixedTableReduction

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284TableFrame
open Shared.Beeping.NPcoNP.Source284UnaryFrameReduction
open Shared.Beeping.NPcoNP.Source284HardnessFramePoly
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284CanonicalConditional (referenceLanguage)
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CanonicalClasses
open Shared.Codes.BitNumeralCompare

/-- An arbitrary but fixed finite binary word can be emitted in canonical
polynomial time. Its machine may depend on the fixed word, not on the input. -/
theorem constList_isPolyTime (code : List Bool) :
    ComplexityTheory.IsPolyTime (fun _ : List Bool => code) := by
  induction code with
  | nil => exact TM2EmptyConstant.isPolyTime [] rfl
  | cons bit tail ih =>
    let first : List Bool → Bool := fun _ => bit
    let rest : List Bool → List Bool := fun _ => tail
    have hf : ComplexityTheory.IsPolyTime first := TM2Constant.isPolyTime bit
    have hp := TM2GuardAllStep.pair_isPolyTime first rest hf ih
    have hc := TM2Compose.isPolyTime_comp (fun x : List Bool => (first x, rest x))
      (TM2ListAppend.cons (α := Bool)) hp TM2ListAppend.cons_isPolyTime
    simpa [first, rest, TM2ListAppend.cons] using hc

/-- The raw bitstring input supplies the length of unary padding. -/
def fixedFrame (n : Nat) (table : Nat → Bool → Row) (pad : List Bool) : List Bool :=
  produceSafe (programBits n table, pad)

theorem fixedFrame_isPolyTime (n : Nat) (table : Nat → Bool → Row) :
    ComplexityTheory.IsPolyTime (fixedFrame n table) := by
  let code : List Bool → List Bool := fun _ => programBits n table
  have hc : ComplexityTheory.IsPolyTime code := constList_isPolyTime _
  have hi : ComplexityTheory.IsPolyTime (id : List Bool → List Bool) :=
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hp := TM2GuardAllStep.pair_isPolyTime code id hc hi
  have h := TM2Compose.isPolyTime_comp (fun x : List Bool => (code x, id x))
    produceSafe hp produceSafe_isPolyTime
  change ComplexityTheory.IsPolyTime (fun pad : List Bool => produceSafe (programBits n table, pad))
  simpa [code] using h

/-- Existential bounded acceptance of one fixed table on zero input, with
the source clock including the fixed code and the supplied unary padding. -/
def tableLanguage (n : Nat) (table : Nat → Bool → Row) (pad : List Bool) : Bool :=
  let t := time (programBits n table, pad)
  (List.range (2 ^ t)).any (fun c => (run table ⟨c, 0, some 0⟩ t).state.isNone)

theorem reference_fixedFrame (n : Nat) (table : Nat → Bool → Row)
    (hn : 0 < n) (closed : Closed n table) (pad : List Bool) :
    referenceLanguage (fixedFrame n table pad) = tableLanguage n table pad := by
  unfold referenceLanguage fixedFrame tableLanguage
  rw [reduction_correct]
  simp only [boundedSource, programBits_value, acceptBound]
  congr 1
  funext c
  exact bounded_acceptance n table 0 hn closed 0 c _

/-- A uniform reduction on all raw bitstrings, for each table fixed in
advance. This alone provides no hardness for arbitrary input languages. -/
theorem fixedTable_polyRed (n : Nat) (table : Nat → Bool → Row)
    (hn : 0 < n) (closed : Closed n table) :
    PolyRed (tableLanguage n table) referenceLanguage := by
  exact ⟨fixedFrame n table, fixedFrame_isPolyTime n table,
    fun pad => (reference_fixedFrame n table hn closed pad).symm⟩

end Shared.Beeping.NPcoNP.Source284FixedTableReduction
