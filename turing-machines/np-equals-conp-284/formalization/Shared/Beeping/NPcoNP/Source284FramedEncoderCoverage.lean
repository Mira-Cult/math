import Shared.Beeping.NPcoNP.Source284FramedEncoder

/-! Raw-input and valid bounded tagged-witness coverage for the finite
serializer and encoder-prefix source execution. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284FramedEncoderCoverage

open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros)
open Shared.Beeping.NPcoNP.Source284FramedEncoderTable (Codec word)
open Shared.Beeping.NPcoNP.Source284FramedEncoder
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Codes.FinitePrograms (Program Tape valid run initial)
open Shared.ComplexityBridge.TM2BinaryPostCosts (inputBits)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284CompileRecords (codeState)

theorem decoded_encoder_window {width : Nat} (enc : Codec width) (next : Program)
    (hn : valid next = true) (k limit certificate : Nat) (x w : List Bool)
    (inputSuffix radiusSource radiusEncoder fuel q : Nat) (reference : Tape)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w)
    (hrun : run next (initial (inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits x w))) fuel = some (.inr (q,reference)))
    (hinputFit : radiusEncoder+fuel-(2*(inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits x w)).length+3) ≤ k*(x.length*x.length)+2)
    (hwitnessFit : (word enc).length+(radiusSource+serialClock enc x w fuel) ≤
      firstZeros k x.length+2*x.length+4) :
    ∃ witnessSuffix actualTape rev revSource,
      certificate=4*encodeFrame w witnessSuffix ∧
      Window radiusEncoder (represented actualTape rev (codeState q rev))
        (represented reference rev (codeState q rev)) ∧
      Window radiusSource
        (Source284Relative.run (sourceDescription enc next k)
          (Source284Relative.initial (encodeFrame x inputSuffix) certificate)
          (sourceTime enc k x w fuel))
        (Source284SourceRelocation.lift (1292+220*k) (target enc next (q,actualTape) revSource)) := by
  obtain ⟨suffix,hcert⟩ := Source284CertificateProbeSource.decoded_has_frame limit certificate w hdec
  obtain ⟨actualTape,rev,revSource,henc,hsource⟩ := source_encoder_window enc next hn k x w inputSuffix suffix
    radiusSource radiusEncoder fuel q reference hrun hinputFit hwitnessFit
  refine ⟨suffix,actualTape,rev,revSource,hcert,henc,?_⟩
  rw [hcert]
  exact hsource

theorem all_inputs_encoder_window {width : Nat} (enc : Codec width) (next : Program)
    (hn : valid next = true) (k limit input certificate : Nat) (w : List Bool)
    (radiusSource radiusEncoder fuel q : Nat) (reference : Tape)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w)
    (hrun : run next (initial (inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits (Source284RawParse.payload input.bits) w))) fuel =
        some (.inr (q,reference)))
    (hinputFit : radiusEncoder+fuel-(2*(inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits (Source284RawParse.payload input.bits) w)).length+3) ≤
        k*(Source284Parser.length input*Source284Parser.length input)+2)
    (hwitnessFit : (word enc).length+(radiusSource+serialClock enc (Source284RawParse.payload input.bits) w fuel) ≤
      firstZeros k (Source284Parser.length input)+2*Source284Parser.length input+4) :
    ∃ inputSuffix witnessSuffix actualTape rev revSource,
      input=encodeFrame (Source284RawParse.payload input.bits) inputSuffix ∧
      certificate=4*encodeFrame w witnessSuffix ∧
      Window radiusEncoder (represented actualTape rev (codeState q rev))
        (represented reference rev (codeState q rev)) ∧
      Window radiusSource
        (Source284Relative.run (sourceDescription enc next k) (Source284Relative.initial input certificate)
          (sourceTime enc k (Source284RawParse.payload input.bits) w fuel))
        (Source284SourceRelocation.lift (1292+220*k) (target enc next (q,actualTape) revSource)) := by
  obtain ⟨x,suffix,hframe⟩ := Source284Parser.encodeFrame_surjective input
  have hp : Source284RawParse.payload input.bits=x := by
    rw [← hframe]
    exact Source284NormalizedWindow.payload_encodeFrame x suffix
  have hlen : Source284Parser.length input=x.length := by
    rw [← hframe]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  have hrun' : run next (initial (inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits x w))) fuel = some (.inr (q,reference)) := by simpa [hp] using hrun
  have hi : radiusEncoder+fuel-(2*(inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits x w)).length+3) ≤ k*(x.length*x.length)+2 := by
    simpa [hp,hlen] using hinputFit
  have hw : (word enc).length+(radiusSource+serialClock enc x w fuel) ≤ firstZeros k x.length+2*x.length+4 := by
    simpa [hp,hlen] using hwitnessFit
  obtain ⟨ws,actualTape,rev,revSource,hcert,henc,hsource⟩ :=
    decoded_encoder_window enc next hn k limit certificate x w suffix radiusSource radiusEncoder fuel q reference
      hdec hrun' hi hw
  refine ⟨suffix,ws,actualTape,rev,revSource,?_,hcert,henc,?_⟩
  · simpa [hp] using hframe.symm
  · rw [hp,← hframe]
    exact hsource

end Shared.Beeping.NPcoNP.Source284FramedEncoderCoverage
