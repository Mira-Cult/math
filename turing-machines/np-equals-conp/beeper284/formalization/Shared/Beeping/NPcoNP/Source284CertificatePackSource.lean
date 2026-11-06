import Shared.Beeping.NPcoNP.Source284CertificatePackSeek
import Shared.Beeping.NPcoNP.Source284CertificateProbeSource

/-! A finite source program takes the actual tagged witness beyond the paid
quadratic workspace, packs every witness bit into a self-delimited scratch
stream, and follows an arbitrary finite continuation. This is not yet the
canonical pair-window loader or the physical 284-state refinement. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284CertificatePackSource

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284TwoSidedScaledQuadraticWindow (leftData rightData)
open Shared.Beeping.NPcoNP.Source284CertificateProbeRun (body)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros secondZeros)
open Shared.Beeping.NPcoNP.Source284CertificatePackSeek (seekCost inputSide)
open Shared.Beeping.NPcoNP.Source284PayloadLoop (scratch)
open Shared.Beeping.NPcoNP.Source284ScratchTerminator (mark)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284CertificatePackSeek.table (Source284ScratchPack.table continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (138+states) (table continuation) := by
  have h := Source284CertificatePackSeek.closed (133+states) (Source284ScratchPack.table continuation)
    (by omega) (Source284ScratchPack.closed states continuation hn hv)
  change Closed (5+(133+states)) (table continuation) at h
  convert h using 1 <;> omega

def packCost (z1 z2 : Nat) (w : List Bool) := seekCost z1 z2+Source284ScratchPack.totalCost w.length

/-- The witness is packed in full, while the complete input-side stream is
preserved on the opposite tape. The packer retains the suffix above its two
explicitly marked low cells. -/
theorem pack_then (states : Nat) (continuation : Nat → Bool → Row)
    (z1 z2 stream suffix : Nat) (w : List Bool) (fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    run (table continuation) ⟨body z1 z2 (encodeFrame w suffix),2*stream,some 0⟩
      (packCost z1 z2 w+fuel) =
    shiftConfig 138 (run continuation
      ⟨inputSide z1 z2 stream,encodeFrame [] (scratch w (mark suffix)),some 0⟩ fuel) := by
  have ht : packCost z1 z2 w+fuel = seekCost z1 z2+(Source284ScratchPack.totalCost w.length+fuel) := by
    simp [packCost]; omega
  rw [ht]
  unfold table
  rw [Source284CertificatePackSeek.seek_then,Source284ScratchScanner.run_add,
    Source284WitnessScratch.pack states continuation w (inputSide z1 z2 stream) suffix hn hv]
  change shiftConfig 5 (run (Source284ScratchPack.table continuation)
    (shiftConfig 133 ⟨inputSide z1 z2 stream,encodeFrame [] (scratch w (mark suffix)),some 0⟩) fuel) = _
  rw [Source284WitnessScratch.pack_after,Source284SourceRelocation.shiftConfig_add]

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284TwoSidedScaledQuadratic.description k (138+states) (table continuation)

def stream (k : Nat) (input : List Bool) (suffix : Nat) : Nat :=
  flipped (input++[false]) (2^(k*(input.length*input.length)+1)*
    Source284TwoSidedScaledQuadratic.finalTail k input.length suffix)

def totalCost (k : Nat) (input witness : List Bool) : Nat :=
  Source284TwoSidedScaledQuadratic.totalCost k input+
    packCost (firstZeros k input.length) (secondZeros input.length) witness

/-- From the actual raw input and tagged frame, reach the packed complete
witness in a finite number of source steps, with every subsequent continuation
step agreeing exactly. -/
theorem source_pack_then (k states : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (witnessSuffix inputSuffix fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (encodeFrame input inputSuffix) (4*encodeFrame witness witnessSuffix))
      (totalCost k input witness+fuel) =
    toSource (shiftConfig (978+220*k) (run continuation
      ⟨inputSide (firstZeros k input.length) (secondZeros input.length) (stream k input inputSuffix),
        encodeFrame [] (scratch witness (mark witnessSuffix)),some 0⟩ fuel)) := by
  have hc := closed states continuation hn hv
  have hp := Source284TwoSidedScaledQuadratic.source_then k (138+states)
    (table continuation) input (4*encodeFrame witness witnessSuffix) inputSuffix
    (packCost (firstZeros k input.length) (secondZeros input.length) witness+fuel) (by omega) hc
  have ht : totalCost k input witness+fuel = Source284TwoSidedScaledQuadratic.totalCost k input+
      (packCost (firstZeros k input.length) (secondZeros input.length) witness+fuel) := by
    simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284TwoSidedScaledQuadratic.description k (138+states)
    (table continuation)) (Source284Relative.initial (encodeFrame input inputSuffix)
      (4*encodeFrame witness witnessSuffix)) _ = _
  rw [hp]
  change toSource (shiftConfig (840+220*k) (run (table continuation)
    ⟨leftData k input (4*encodeFrame witness witnessSuffix),rightData k input inputSuffix,some 0⟩ _)) = _
  rw [Source284CertificateProbeLayout.leftData_eq_body]
  change toSource (shiftConfig (840+220*k) (run (table continuation)
    ⟨body (firstZeros k input.length) (secondZeros input.length) (encodeFrame witness witnessSuffix),
      2*stream k input inputSuffix,some 0⟩ _)) = _
  rw [pack_then states continuation _ _ _ _ witness fuel hn hv,Source284SourceRelocation.shiftConfig_add]
  have he : 840+220*k+138=978+220*k := by omega
  rw [he]

/-- This covers every valid bounded certificate, including high-suffix aliases;
all witness bits are present in the scratch stream, not only the first bit. -/
theorem decoded_pack_then (k states limit certificate : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (inputSuffix fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some witness) :
    ∃ witnessSuffix,
      certificate=4*encodeFrame witness witnessSuffix ∧
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial (encodeFrame input inputSuffix) certificate)
        (totalCost k input witness+fuel) =
      toSource (shiftConfig (978+220*k) (run continuation
        ⟨inputSide (firstZeros k input.length) (secondZeros input.length) (stream k input inputSuffix),
          encodeFrame [] (scratch witness (mark witnessSuffix)),some 0⟩ fuel)) := by
  obtain ⟨suffix,hcert⟩ := Source284CertificateProbeSource.decoded_has_frame limit certificate witness hdec
  refine ⟨suffix,hcert,?_⟩
  rw [hcert]
  exact source_pack_then k states continuation input witness suffix inputSuffix fuel hn hv

theorem packed_decodes (w : List Bool) (suffix : Nat) :
    Source284ScratchDecode.decode (scratch w (mark suffix)) = some w ∧
      Source284ScratchDecode.inspections (scratch w (mark suffix)) = w.length+1 :=
  Source284ScratchPack.output_decodes w suffix

/-- Bound for the seek and pack stages, after the workspace initialization. -/
theorem packCost_bound (k n limit certificate : Nat) (w : List Bool)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    packCost (firstZeros k n) (secondZeros n) w ≤
      k*(n*n)+8*n+12+2*limit*limit+18*limit+16 := by
  have hlen := Source284TaggedWitnessCodec.decode_length limit certificate w hdec
  have hsq : w.length*w.length ≤ limit*limit := Nat.mul_self_le_mul_self hlen
  unfold packCost seekCost firstZeros secondZeros
  rw [Source284ScratchPack.totalCost_formula]
  nlinarith

/-- Every natural input is covered, including zero and arbitrary ignored
input suffixes; validity of the tagged certificate is still explicit. -/
theorem all_inputs_decoded_pack_then (k states limit input certificate : Nat)
    (continuation : Nat → Bool → Row) (witness : List Bool) (fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some witness) :
    ∃ inputBits inputSuffix witnessSuffix,
      input = encodeFrame inputBits inputSuffix ∧
      inputBits.length = Source284Parser.length input ∧
      certificate = 4*encodeFrame witness witnessSuffix ∧
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial input certificate) (totalCost k inputBits witness+fuel) =
      toSource (shiftConfig (978+220*k) (run continuation
        ⟨inputSide (firstZeros k inputBits.length) (secondZeros inputBits.length) (stream k inputBits inputSuffix),
          encodeFrame [] (scratch witness (mark witnessSuffix)),some 0⟩ fuel)) := by
  obtain ⟨inputBits,inputSuffix,hinput⟩ := Source284Parser.encodeFrame_surjective input
  obtain ⟨witnessSuffix,hcert,hresult⟩ := decoded_pack_then k states limit certificate continuation
    inputBits witness inputSuffix fuel hn hv hdec
  refine ⟨inputBits,inputSuffix,witnessSuffix,hinput.symm,?_,hcert,?_⟩
  · rw [← hinput]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  · rw [← hinput]
    exact hresult

/-- End-to-end loader plus packer time, with a supplied witness cutoff.
Multiplication by three clears the exact initialization formula's denominator. -/
theorem totalCost_bound (k limit certificate : Nat) (input witness : List Bool)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some witness) :
    3*totalCost k input witness ≤
      6*k*k*input.length^4+(16+48*k)*input.length^3+
      (318+273*k)*input.length^2+(1154+264*k)*input.length+1053+156*k+
      3*(k*(input.length*input.length)+8*input.length+12+2*limit*limit+18*limit+16) := by
  have h0 := Source284TwoSidedScaledQuadratic.totalCost_formula k input
  have h1 := packCost_bound k input.length limit certificate witness hdec
  unfold totalCost
  omega

end Shared.Beeping.NPcoNP.Source284CertificatePackSource
