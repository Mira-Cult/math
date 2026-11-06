import Shared.Beeping.NPcoNP.Source284FramedSerialize

/-! Coverage of the raw-input serializer composition for valid bounded tagged
witnesses, with the finite-window size requirement explicit. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284FramedSerializeCoverage

open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros)
open Shared.Beeping.NPcoNP.Source284FramedSerializeTable
open Shared.Beeping.NPcoNP.Source284FramedSerialize
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.ComplexityBridge.TM2BinaryPostCosts (inputBits)

theorem serialized_words {width : Nat} (enc : Codec width) (x w : List Bool) :
    out enc x w = inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits x w) := by
  exact Source284ClearedUntagSource.serialized_words enc x w (rest x w) false (body_reverse x w)

theorem decoded_serialize_window {width : Nat} (enc : Codec width)
    (k limit certificate : Nat) (x w : List Bool) (inputSuffix radius : Nat)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w)
    (hfit : (word enc).length+(radius+serialClock enc x w) ≤
      firstZeros k x.length+2*x.length+4) :
    ∃ witnessSuffix rev,
      certificate=4*encodeFrame w witnessSuffix ∧
      Window radius
        (Source284Relative.run (sourceDescription enc k)
          (Source284Relative.initial (encodeFrame x inputSuffix) certificate)
          (sourceTime enc k x w))
        (Source284SourceRelocation.lift (1286+220*k) (target enc x w (inputList k x inputSuffix) rev)) := by
  obtain ⟨suffix,hcert⟩ := Source284CertificateProbeSource.decoded_has_frame limit certificate w hdec
  obtain ⟨rev,hwindow⟩ := source_serialize_window enc k x w inputSuffix suffix radius hfit
  refine ⟨suffix,rev,hcert,?_⟩
  rw [hcert]
  exact hwindow

theorem all_inputs_serialize_window {width : Nat} (enc : Codec width)
    (k limit input certificate : Nat) (w : List Bool) (radius : Nat)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w)
    (hfit : (word enc).length+(radius+serialClock enc (Source284RawParse.payload input.bits) w) ≤
      firstZeros k (Source284Parser.length input)+2*Source284Parser.length input+4) :
    ∃ inputSuffix witnessSuffix rev,
      input=encodeFrame (Source284RawParse.payload input.bits) inputSuffix ∧
      certificate=4*encodeFrame w witnessSuffix ∧
      Window radius
        (Source284Relative.run (sourceDescription enc k)
          (Source284Relative.initial input certificate)
          (sourceTime enc k (Source284RawParse.payload input.bits) w))
        (Source284SourceRelocation.lift (1286+220*k)
          (target enc (Source284RawParse.payload input.bits) w
            (inputList k (Source284RawParse.payload input.bits) inputSuffix) rev)) := by
  obtain ⟨x,suffix,hframe⟩ := Source284Parser.encodeFrame_surjective input
  have hp : Source284RawParse.payload input.bits=x := by
    rw [← hframe]
    exact Source284NormalizedWindow.payload_encodeFrame x suffix
  have hn : Source284Parser.length input=x.length := by
    rw [← hframe]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  have hfit' : (word enc).length+(radius+serialClock enc x w) ≤
      firstZeros k x.length+2*x.length+4 := by simpa [hp,hn] using hfit
  obtain ⟨ws,rev,hcert,hw⟩ := decoded_serialize_window enc k limit certificate x w suffix radius hdec hfit'
  refine ⟨suffix,ws,rev,?_,hcert,?_⟩
  · simpa [hp] using hframe.symm
  · rw [hp,← hframe]
    exact hw

end Shared.Beeping.NPcoNP.Source284FramedSerializeCoverage
