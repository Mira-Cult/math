import Shared.Beeping.NPcoNP.Source284CertificateCompact

/-! Input coverage, explicit data recovery, and total time bound for the
quadratic-loader to compacted-witness composition. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284CertificateCompactCoverage

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros)
open Shared.Beeping.NPcoNP.Source284CertificatePackSource (stream)
open Shared.Beeping.NPcoNP.Source284CertificateCompact
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

/-- Decoding the compacted witness is independent of the high suffix. This
is a mathematical decoder theorem, not an implementation of a verifier. -/
theorem witness_recovers (w : List Bool) (suffix : Nat) :
    Source284ScratchFlipDecode.decode (flipped w (4*(suffix/4))) = some w :=
  Source284ScratchFlipDecode.decode_flipped w _

/-- These divisions describe the retained input-side stream mathematically;
no machine-time claim for this recovery expression is made here. -/
def recoverStream (z n data : Nat) : Nat := ((data / 2^(2*n))/2 / 2^z)/2

theorem recover_inner (z n x : Nat) : recoverStream z n (innerInput z n x) = x := by
  have h (a : Nat) : (2*a+1)/2=a := by omega
  unfold recoverStream innerInput
  rw [Nat.mul_div_cancel_left _ (Nat.two_pow_pos _),h,
    Nat.mul_div_cancel_left _ (Nat.two_pow_pos _),h]

theorem input_recovers (k : Nat) (input : List Bool) (suffix : Nat) :
    Source284ScratchFlipDecode.decode
      (recoverStream (firstZeros k input.length) input.length
        (innerInput (firstZeros k input.length) input.length (stream k input suffix))) =
      some (input++[false]) := by
  rw [recover_inner]
  exact Source284ScratchFlipDecode.decode_flipped _ _

/-- Every natural input is covered, including zero and arbitrary ignored
input suffixes; validity of the tagged certificate is still explicit. -/
theorem all_inputs_decoded_compact_then (k states limit input certificate : Nat)
    (continuation : Nat → Bool → Row) (witness : List Bool) (fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some witness) :
    ∃ inputBits inputSuffix witnessSuffix,
      input = encodeFrame inputBits inputSuffix ∧
      inputBits.length = Source284Parser.length input ∧
      certificate = 4*encodeFrame witness witnessSuffix ∧
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial input certificate) (totalCost k inputBits witness+fuel) =
      toSource (shiftConfig (1005+220*k) (run continuation
        ⟨4*innerInput (firstZeros k inputBits.length) inputBits.length (stream k inputBits inputSuffix)+1,
          2*flipped witness (4*(witnessSuffix/4)),some 0⟩ fuel)) := by
  obtain ⟨inputBits,inputSuffix,hinput⟩ := Source284Parser.encodeFrame_surjective input
  obtain ⟨witnessSuffix,hcert,hresult⟩ := decoded_compact_then k states limit certificate continuation
    inputBits witness inputSuffix fuel hn hv hdec
  refine ⟨inputBits,inputSuffix,witnessSuffix,hinput.symm,?_,hcert,?_⟩
  · rw [← hinput]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  · rw [← hinput]
    exact hresult

/-- End-to-end source initialization plus full witness compaction has a
uniform polynomial bound in input length and the original witness cutoff. -/
theorem totalCost_bound (k limit certificate : Nat) (input witness : List Bool)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some witness) :
    3*totalCost k input witness ≤
      6*k*k*input.length^4+(16+48*k)*input.length^3+
      (318+273*k)*input.length^2+(1154+264*k)*input.length+1053+156*k+
      3*(k*(input.length*input.length)+8*input.length+60+2*limit*limit+38*limit) := by
  have h0 := Source284TwoSidedScaledQuadratic.totalCost_formula k input
  have h1 := compactCost_bound k input.length limit certificate witness hdec
  unfold totalCost
  omega

end Shared.Beeping.NPcoNP.Source284CertificateCompactCoverage
