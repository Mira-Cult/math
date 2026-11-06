import Shared.Beeping.NPcoNP.Source284HardwireGuarded
import Shared.ComplexityBridge.TM2CircuitTemplate

/-! A linear unary padding construction for the hardwired guarded-table
reference. The original cutoff is supplied as the length of an explicit bit
list. This does not serialize a table or construct a SAT reduction. -/

namespace Shared.Beeping.NPcoNP.Source284LinearPaddingTM2

open Shared.ComplexityBridge
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable
open Shared.Beeping.NPcoNP.Source284HardwireGuarded
open Shared.Beeping.NPcoNP.Source284TableFrame
open Shared.Beeping.NPcoNP.Source284TableClock
open Shared.Beeping.NPcoNP.Source284HardnessFramePoly
open Shared.Beeping.NPcoNP.Source284Comparison

abbrev Input := List Bool × (List Bool × List Bool)

/-- Public bits are counted twice for the loader, and the cutoff list is
counted once. The values of all padding bits are irrelevant. -/
def padding (p : List Bool × List Bool) : List Bool :=
  p.1 ++ p.1 ++ p.2 ++ [false, false]

def frame (p : Input) : List Bool := produceSafe (p.1, padding p.2)

theorem padding_length (p : List Bool × List Bool) :
    (padding p).length = offset p.1 + p.2.length := by
  simp [padding, offset]
  omega

theorem padding_isPolyTime : ComplexityTheory.IsPolyTime padding := by
  let first : List Bool × List Bool → List Bool := fun p => p.1
  let second : List Bool × List Bool → List Bool := fun p => p.2
  let last : List Bool × List Bool → List Bool := fun _ => [false, false]
  have hf : ComplexityTheory.IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hs : ComplexityTheory.IsPolyTime second := TM2GuardAllStep.second_isPolyTime
  have hl : ComplexityTheory.IsPolyTime last := by
    have hfalse : ComplexityTheory.IsPolyTime (fun _ : List Bool × List Bool => false) :=
      TM2Constant.isPolyTime false
    simpa [last] using TM2GateCNFPieces.pairList_isPolyTime
      (fun _ : List Bool × List Bool => false) (fun _ => false) hfalse hfalse
  have h2 := TM2CircuitTemplate.append_isPolyTime second last hs hl
  have h3 := TM2CircuitTemplate.append_isPolyTime first (fun p => second p ++ last p) hf h2
  have h4 := TM2CircuitTemplate.append_isPolyTime first
    (fun p => first p ++ (second p ++ last p)) hf h3
  change ComplexityTheory.IsPolyTime (fun p : List Bool × List Bool =>
    p.1 ++ p.1 ++ p.2 ++ [false, false])
  simpa [first, second, last, List.append_assoc] using h4

theorem frame_isPolyTime : ComplexityTheory.IsPolyTime frame := by
  let code : Input → List Bool := fun p => p.1
  let rest : Input → List Bool × List Bool := fun p => p.2
  have hc : ComplexityTheory.IsPolyTime code := TM2PairFirst.first_isPolyTime
  have hr : ComplexityTheory.IsPolyTime rest := TM2GuardAllStep.second_isPolyTime
  have hp : ComplexityTheory.IsPolyTime (fun p : Input => padding (rest p)) :=
    TM2Compose.isPolyTime_comp rest padding hr padding_isPolyTime
  have hpair := TM2GuardAllStep.pair_isPolyTime code (fun p => padding (rest p)) hc hp
  have h := TM2Compose.isPolyTime_comp (fun p : Input => (code p, padding (rest p)))
    produceSafe hpair produceSafe_isPolyTime
  change ComplexityTheory.IsPolyTime (fun p : Input => produceSafe (p.1, padding p.2))
  simpa [code, rest] using h

/-- The chosen padding produces the clock required by the guarded-table
lemma, with extra time exactly the code length plus the separator. -/
theorem frame_eq_guarded_padding (code bits cutoff : List Bool) :
    frame (code, bits, cutoff) =
      produceSafe (code, padFor code (offset bits + (cutoff.length + (code.length + 1)))) := by
  rw [frame, produceSafe_eq_input, produceSafe_eq_input]
  congr 1
  simp [padFor, padding_length]
  omega

/-- Once an independently constructed bit list is known to be the table
serialization, its frame checks exactly the original bounded table answer.
The table remains a Lean function here; no effective serializer is assumed. -/
theorem reference_exact (bits cutoff : List Bool) (original : Nat → Bool → Row)
    (n : Nat) (hn : 0 < n) (hclosed : Closed n original) :
    let code := programBits (offset bits + Source284TableCountdown.allocated n cutoff.length)
      (table bits (Source284TableCountdown.table n cutoff.length original))
    reference (value (frame (code, bits, cutoff))) = true ↔
      ∃ certificate, certificate < 2^cutoff.length ∧
        (run original ⟨certificate,value bits,some 0⟩ cutoff.length).state.isNone = true := by
  dsimp only
  rw [frame_eq_guarded_padding]
  apply reference_guarded_original_bound bits original n cutoff.length hn hclosed
  omega

end Shared.Beeping.NPcoNP.Source284LinearPaddingTM2
