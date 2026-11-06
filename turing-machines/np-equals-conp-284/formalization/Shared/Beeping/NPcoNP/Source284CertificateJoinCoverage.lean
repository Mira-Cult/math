import Shared.Beeping.NPcoNP.Source284CertificateJoin

/-! Coverage and explicit bounds for the adjacent-stream source loader. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284CertificateJoinCoverage

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros)
open Shared.Beeping.NPcoNP.Source284CertificatePackSource (stream)
open Shared.Beeping.NPcoNP.Source284CertificateJoin
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

/-- Both complete streams decode mathematically; this is not yet the
transition-table implementation of the canonical pair encoder. -/
theorem both_recover (k : Nat) (input witness : List Bool) (inputSuffix witnessSuffix : Nat) :
    Source284ScratchFlipDecode.decode (stream k input inputSuffix) = some (input++[false]) ∧
    Source284ScratchFlipDecode.decode
      (flipped witness (witnessTail (firstZeros k input.length) input.length witnessSuffix)) = some witness := by
  constructor <;> exact Source284ScratchFlipDecode.decode_flipped _ _

theorem all_inputs_decoded_join_then (k states limit input certificate : Nat)
    (continuation : Nat → Bool → Row) (witness : List Bool) (fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some witness) :
    ∃ inputBits inputSuffix witnessSuffix,
      input = encodeFrame inputBits inputSuffix ∧
      inputBits.length = Source284Parser.length input ∧
      certificate = 4*encodeFrame witness witnessSuffix ∧
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial input certificate) (totalCost k inputBits witness+fuel) =
      toSource (shiftConfig (1045+220*k) (run continuation
        ⟨2*stream k inputBits inputSuffix,
          2*flipped witness (witnessTail (firstZeros k inputBits.length) inputBits.length witnessSuffix),some 0⟩ fuel)) := by
  obtain ⟨inputBits,inputSuffix,hinput⟩ := Source284Parser.encodeFrame_surjective input
  obtain ⟨witnessSuffix,hcert,hresult⟩ := decoded_join_then k states limit certificate continuation
    inputBits witness inputSuffix fuel hn hv hdec
  refine ⟨inputBits,inputSuffix,witnessSuffix,hinput.symm,?_,hcert,?_⟩
  · rw [← hinput]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  · rw [← hinput]
    exact hresult

theorem finishCost_bound (k n limit certificate : Nat) (w : List Bool)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    finishCost (firstZeros k n) n w ≤ (k*(n*n)+8*n+9)*(8*limit+11)+12 := by
  have hlen := Source284TaggedWitnessCodec.decode_length limit certificate w hdec
  have hprod := Nat.mul_le_mul_left (k*(n*n)+8*n+9) (show 8*w.length+11 ≤ 8*limit+11 by omega)
  unfold finishCost Source284ClearCompact.cost firstZeros
  nlinarith

/-- Total source preparation has a single polynomial bound in input length
and the original witness cutoff, including every sentinel crossing. -/
theorem totalCost_bound (k limit certificate : Nat) (input witness : List Bool)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some witness) :
    3*totalCost k input witness ≤
      6*k*k*input.length^4+(16+48*k)*input.length^3+
      (318+273*k)*input.length^2+(1154+264*k)*input.length+1053+156*k+
      3*(k*(input.length*input.length)+8*input.length+60+2*limit*limit+38*limit)+
      3*((k*(input.length*input.length)+8*input.length+9)*(8*limit+11)+12) := by
  have h0 := Source284CertificateCompactCoverage.totalCost_bound k limit certificate input witness hdec
  have h1 := finishCost_bound k input.length limit certificate witness hdec
  unfold totalCost
  omega

end Shared.Beeping.NPcoNP.Source284CertificateJoinCoverage
