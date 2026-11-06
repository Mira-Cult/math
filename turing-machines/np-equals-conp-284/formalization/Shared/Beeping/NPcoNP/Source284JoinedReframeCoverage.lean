import Shared.Beeping.NPcoNP.Source284JoinedReframe

/-! Full raw-input coverage and cutoff-dependent time bound for the adjacent
normalized-frame source program. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284JoinedReframeCoverage

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros)
open Shared.Beeping.NPcoNP.Source284CertificateJoin (witnessTail)
open Shared.Beeping.NPcoNP.Source284JoinedReframe
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

theorem frames_parse (k : Nat) (input witness : List Bool) (inputSuffix witnessSuffix : Nat) :
    Source284RawParse.payload (encodeFrame input (4*(2*inputTail k input inputSuffix+1))).bits = input ∧
    Source284RawParse.payload (encodeFrame witness
      (2*witnessTail (firstZeros k input.length) input.length witnessSuffix+1)).bits = witness := by
  exact ⟨Source284NormalizedWindow.payload_encodeFrame input _,
    Source284NormalizedWindow.payload_encodeFrame witness _⟩

theorem all_inputs_decoded_reframe_then (k states limit input certificate : Nat)
    (continuation : Nat → Bool → Row) (witness : List Bool) (fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some witness) :
    ∃ inputBits inputSuffix witnessSuffix,
      input = encodeFrame inputBits inputSuffix ∧
      inputBits.length = Source284Parser.length input ∧
      certificate = 4*encodeFrame witness witnessSuffix ∧
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial input certificate) (totalCost k inputBits witness+fuel) =
      toSource (shiftConfig (1251+220*k) (run continuation
        ⟨4*encodeFrame witness (2*witnessTail (firstZeros k inputBits.length) inputBits.length witnessSuffix+1),
          encodeFrame inputBits (4*(2*inputTail k inputBits inputSuffix+1)),some 0⟩ fuel)) := by
  obtain ⟨inputBits,inputSuffix,hinput⟩ := Source284Parser.encodeFrame_surjective input
  obtain ⟨witnessSuffix,hcert,hresult⟩ := decoded_reframe_then k states limit certificate continuation
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
      3*(6*limit+10*input.length+46) := by
  have h0 := Source284CertificateJoinCoverage.totalCost_bound k limit certificate input witness hdec
  have h1 := finishingCost_bound input.length limit certificate input witness hdec rfl
  unfold totalCost
  omega

end Shared.Beeping.NPcoNP.Source284JoinedReframeCoverage
