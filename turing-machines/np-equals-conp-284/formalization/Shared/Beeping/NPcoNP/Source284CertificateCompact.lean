import Shared.Beeping.NPcoNP.Source284CertificatePackSource
import Shared.Beeping.NPcoNP.Source284WitnessCompact

/-! Connect the raw quadratic loader and tagged-frame seek to whole-witness
packing, marker flipping, and the finite sentinel-controlled compaction loop.
The continuation sees the complete witness immediately beside the first
input-side sentinel. Further input serialization remains separate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284CertificateCompact

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284CertificateProbeRun (body)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros secondZeros)
open Shared.Beeping.NPcoNP.Source284CertificatePackSeek (seekCost inputSide)
open Shared.Beeping.NPcoNP.Source284CertificatePackSource (stream)
open Shared.Beeping.NPcoNP.Source284TwoSidedScaledQuadraticWindow (leftData rightData)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284CertificatePackSeek.table (Source284WitnessCompact.table continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (165+states) (table continuation) := by
  have h := Source284CertificatePackSeek.closed (160+states) (Source284WitnessCompact.table continuation)
    (by omega) (Source284WitnessCompact.closed states continuation hn hv)
  change Closed (5+(160+states)) (table continuation) at h
  convert h using 1 <;> omega

/-- The compacting table's two entry modes become identical after two paid
turns. This permits the tag seek to enter in state zero even on empty frames. -/
theorem entry_modes_equal (continuation : Nat → Bool → Row)
    (left right rest : Nat) :
    run (Source284WitnessCompact.table continuation) ⟨left,right,some 0⟩ (2+rest) =
    run (Source284WitnessCompact.table continuation) ⟨left,right,some 1⟩ (2+rest) := by
  unfold Source284WitnessCompact.table
  rw [Source284ScratchScanner.run_add,Source284ScratchScanner.run_add,
    Source284WitnessScratch.enter _ 0 left right (by decide),
    Source284WitnessScratch.enter _ 1 left right (by decide)]

/-- Compaction works from the uniform state-zero entry for either witness
shape; the runtime has no unbounded search for a sentinel. -/
theorem compact_after_seek_zero (states : Nat) (continuation : Nat → Bool → Row)
    (gap inputFrame suffix : Nat) (w : List Bool) (fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    run (Source284WitnessCompact.table continuation)
      ⟨4^(gap+1)*(4*inputFrame+1),encodeFrame w suffix,some 0⟩
      (Source284WitnessCompact.extraCost gap w.length+fuel) =
    shiftConfig 160 (run continuation
      ⟨4*inputFrame+1,2*flipped w (2^(2*(gap+1))*(suffix/4)),some 0⟩ fuel) := by
  have h := Source284WitnessCompact.compact_after_seek states continuation gap inputFrame suffix w fuel hn hv
  change run (Source284WitnessCompact.table continuation) _ _ = _ at h
  cases w with
  | cons b bs => simpa using h
  | nil =>
    simp only [List.length_nil, if_pos rfl] at h ⊢
    have hc : Source284WitnessCompact.extraCost gap 0+fuel =
        2+(Source284WitnessCompact.extraCost gap 0+fuel-2) := by
      simp [Source284WitnessCompact.extraCost]; omega
    rw [hc,entry_modes_equal]
    rw [hc] at h
    simpa using h

/-- The second zero run is odd in length, so the exact seek output matches
one zero-pair gap in front of the next input-side sentinel. -/
def innerInput (z1 n stream : Nat) : Nat :=
  2^(2*n)*(2*(2^z1*(2*stream+1))+1)

theorem inputSide_shape (z1 n stream : Nat) :
    inputSide z1 (secondZeros n) stream = 4^(0+1)*(4*innerInput z1 n stream+1) := by
  simp [inputSide,secondZeros,innerInput,pow_succ]
  ring

def compactCost (z1 n : Nat) (w : List Bool) :=
  seekCost z1 (secondZeros n)+Source284WitnessCompact.extraCost 0 w.length

theorem compact_then (states : Nat) (continuation : Nat → Bool → Row)
    (z1 n stream suffix : Nat) (w : List Bool) (fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    run (table continuation) ⟨body z1 (secondZeros n) (encodeFrame w suffix),2*stream,some 0⟩
      (compactCost z1 n w+fuel) =
    shiftConfig 165 (run continuation
      ⟨4*innerInput z1 n stream+1,2*flipped w (4*(suffix/4)),some 0⟩ fuel) := by
  have ht : compactCost z1 n w+fuel = seekCost z1 (secondZeros n)+
      (Source284WitnessCompact.extraCost 0 w.length+fuel) := by simp [compactCost]; omega
  rw [ht]
  unfold table
  rw [Source284CertificatePackSeek.seek_then,inputSide_shape,
    compact_after_seek_zero states continuation 0 (innerInput z1 n stream) suffix w fuel hn hv,
    Source284SourceRelocation.shiftConfig_add]
  congr 2 <;> simp

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284TwoSidedScaledQuadratic.description k (165+states) (table continuation)

def totalCost (k : Nat) (input witness : List Bool) : Nat :=
  Source284TwoSidedScaledQuadratic.totalCost k input+
    compactCost (firstZeros k input.length) input.length witness

/-- Raw input and valid frame reach the fully packed witness beside the
first sentinel, then follow every continuation step exactly. -/
theorem source_compact_then (k states : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (witnessSuffix inputSuffix fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (encodeFrame input inputSuffix) (4*encodeFrame witness witnessSuffix))
      (totalCost k input witness+fuel) =
    toSource (shiftConfig (1005+220*k) (run continuation
      ⟨4*innerInput (firstZeros k input.length) input.length (stream k input inputSuffix)+1,
        2*flipped witness (4*(witnessSuffix/4)),some 0⟩ fuel)) := by
  have hc := closed states continuation hn hv
  have hp := Source284TwoSidedScaledQuadratic.source_then k (165+states)
    (table continuation) input (4*encodeFrame witness witnessSuffix) inputSuffix
    (compactCost (firstZeros k input.length) input.length witness+fuel) (by omega) hc
  have ht : totalCost k input witness+fuel = Source284TwoSidedScaledQuadratic.totalCost k input+
      (compactCost (firstZeros k input.length) input.length witness+fuel) := by simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284TwoSidedScaledQuadratic.description k (165+states)
    (table continuation)) (Source284Relative.initial (encodeFrame input inputSuffix)
      (4*encodeFrame witness witnessSuffix)) _ = _
  rw [hp]
  change toSource (shiftConfig (840+220*k) (run (table continuation)
    ⟨leftData k input (4*encodeFrame witness witnessSuffix),rightData k input inputSuffix,some 0⟩ _)) = _
  rw [Source284CertificateProbeLayout.leftData_eq_body]
  change toSource (shiftConfig (840+220*k) (run (table continuation)
    ⟨body (firstZeros k input.length) (secondZeros input.length) (encodeFrame witness witnessSuffix),
      2*stream k input inputSuffix,some 0⟩ _)) = _
  rw [compact_then states continuation _ _ _ _ witness fuel hn hv,Source284SourceRelocation.shiftConfig_add]
  have he : 840+220*k+165=1005+220*k := by omega
  rw [he]

theorem decoded_compact_then (k states limit certificate : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (inputSuffix fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some witness) :
    ∃ witnessSuffix,
      certificate=4*encodeFrame witness witnessSuffix ∧
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial (encodeFrame input inputSuffix) certificate)
        (totalCost k input witness+fuel) =
      toSource (shiftConfig (1005+220*k) (run continuation
        ⟨4*innerInput (firstZeros k input.length) input.length (stream k input inputSuffix)+1,
          2*flipped witness (4*(witnessSuffix/4)),some 0⟩ fuel)) := by
  obtain ⟨suffix,hcert⟩ := Source284CertificateProbeSource.decoded_has_frame limit certificate witness hdec
  refine ⟨suffix,hcert,?_⟩
  rw [hcert]
  exact source_compact_then k states continuation input witness suffix inputSuffix fuel hn hv

theorem compactCost_bound (k n limit certificate : Nat) (w : List Bool)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    compactCost (firstZeros k n) n w ≤ k*(n*n)+8*n+60+2*limit*limit+38*limit := by
  have hlen := Source284TaggedWitnessCodec.decode_length limit certificate w hdec
  have hsq : w.length*w.length ≤ limit*limit := Nat.mul_self_le_mul_self hlen
  unfold compactCost seekCost firstZeros secondZeros Source284WitnessCompact.extraCost
  rw [Source284ScratchPack.totalCost_formula]
  nlinarith

end Shared.Beeping.NPcoNP.Source284CertificateCompact
