import Shared.Beeping.NPcoNP.Source284FramedJoin

/-! All raw inputs and bounded tagged witnesses reach the existing joined
prefix, with a polynomial source-time bound. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284FramedJoinCoverage

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros)
open Shared.Beeping.NPcoNP.Source284CertificateJoin (witnessTail)
open Shared.Beeping.NPcoNP.Source284JoinedReframe (inputTail)
open Shared.Beeping.NPcoNP.Source284FramedJoin
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)

theorem all_inputs_decoded_joined_then (k states limit input certificate : Nat)
    (continuation : Nat → Bool → Row) (witness : List Bool) (fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some witness) :
    ∃ inputBits inputSuffix witnessSuffix,
      input = encodeFrame inputBits inputSuffix ∧
      inputBits.length = Source284Parser.length input ∧
      certificate = 4*encodeFrame witness witnessSuffix ∧
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial input certificate) (totalCost k inputBits witness+fuel) =
      toSource (shiftConfig (1286+220*k) (run continuation
        ⟨4*(2*inputTail k inputBits inputSuffix+1),
          stack (Source284JoinedFrames.joinedBits inputBits witness)
            (witnessTail (firstZeros k inputBits.length) inputBits.length witnessSuffix/2),some 0⟩ fuel)) := by
  obtain ⟨inputBits,inputSuffix,hinput⟩ := Source284Parser.encodeFrame_surjective input
  obtain ⟨witnessSuffix,hcert,hresult⟩ := decoded_joined_then k states limit certificate continuation
    inputBits witness inputSuffix fuel hn hv hdec
  refine ⟨inputBits,inputSuffix,witnessSuffix,hinput.symm,?_,hcert,?_⟩
  · rw [← hinput]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  · rw [← hinput]
    exact hresult

theorem totalCost_bound (k limit certificate : Nat) (input witness : List Bool)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some witness) :
    3*totalCost k input witness ≤
      6*k*k*input.length^4+(16+48*k)*input.length^3+
      (318+273*k)*input.length^2+(1154+264*k)*input.length+1053+156*k+
      3*(k*(input.length*input.length)+8*input.length+60+2*limit*limit+38*limit)+
      3*((k*(input.length*input.length)+8*input.length+9)*(8*limit+11)+12)+
      3*(10*limit+12*input.length+64) := by
  have h0 := Source284CertificateJoinCoverage.totalCost_bound k limit certificate input witness hdec
  have h1 := finishingCost_bound limit certificate input witness hdec
  unfold totalCost
  omega

/-- Every high bit suffix remains irrelevant to parsing the exact joined
prefix. This is the existing parser theorem, not a serializer execution. -/
theorem joined_decodes (input witness extra : List Bool) :
    Source284JoinedFrames.decodeJoined (Source284JoinedFrames.joinedBits input witness ++ extra) =
      some (input,witness) := Source284JoinedFrames.decodeJoined_complete input witness extra

end Shared.Beeping.NPcoNP.Source284FramedJoinCoverage
