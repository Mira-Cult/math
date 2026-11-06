import Shared.Beeping.NPcoNP.Source284BothFrames

/-! Exact continuation after the finite two-frame prefix. This is a source
execution theorem, not an event-preserving physical compiler certificate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284BothFramesContinue

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284RawParse (payload)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift lift_toSource shiftConfig_add)

/-- All later steps after the normalizer agree with the supplied finite
continuation, including accepting state and both entire tape halves. -/
theorem normalize_continuation (states : Nat) (continuation : Nat → Bool → Row)
    (left right fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (Source284ScratchNormalizePipeline.description states continuation)
      ⟨left,right,active 210⟩ fuel =
    lift 210 (Source284Relative.run (encode states continuation 1) ⟨left,right,active 0⟩ fuel) := by
  let c : Config := ⟨left,right,some 0⟩
  have hc : Valid states c := by intro q hq; simp [c] at hq; subst q; exact hn
  have hnorm : Closed (68+states) (Source284ScratchNormalize.table continuation) := by
    have h := Source284ScratchNormalize.closed states continuation hn hv
    have he : 36+(32+states) = 68+states := by omega
    simpa only [he] using h
  have hvalid : Valid (142+(68+states))
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 (shiftConfig 36 (shiftConfig 32 c))))))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q; omega
  have hs := Source284ScratchNormalizePipeline.source_continuation_run (68+states)
    (Source284ScratchNormalize.table continuation) (shiftConfig 36 (shiftConfig 32 c))
    fuel (by omega) hnorm hvalid
  change Source284Relative.run (Source284ScratchNormalizePipeline.description states continuation)
    ⟨left,right,active 210⟩ fuel = _ at hs
  rw [Source284ScratchNormalize.relocated_run,Source284ModePrefixReturn.relocated_run] at hs
  repeat rw [shiftConfig_add] at hs
  have hv0 := run_toSource states continuation 1 c hv hc fuel
  change Source284Relative.run (encode states continuation 1) ⟨left,right,active 0⟩ fuel = _ at hv0
  rw [← lift_toSource,← hv0] at hs
  exact hs

/-- The input normalizer has a positive finite prefix and then exactly
follows the supplied continuation with the full configuration relocated. -/
theorem normalize_after (states : Nat) (continuation : Nat → Bool → Row)
    (x : List Bool) (suffix left fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (Source284ScratchNormalizePipeline.description states continuation)
      (Source284Relative.initial (encodeFrame x suffix) left)
      (Source284ScratchNormalizePipeline.totalCost x.length+fuel) =
    lift 210 (Source284Relative.run (encode states continuation 1)
      ⟨2*left,encodeFrame x (2*(suffix/4)+1),active 0⟩ fuel) := by
  rw [Source284Relative.run_add_clock,
    Source284ScratchNormalizePipeline.source_pipeline states continuation x left suffix hn hv,
    normalize_continuation states continuation (2*left) (encodeFrame x (2*(suffix/4)+1)) fuel hn hv]

/-- The full paid prefix reaches both frames and follows the continuation
for every subsequent clock. The witness and input suffixes stay explicit. -/
theorem both_frames_after (states : Nat) (continuation : Nat → Bool → Row)
    (limit certificate input : Nat) (w : List Bool)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    ∃ witnessSuffix inputSuffix,
      certificate = 4*encodeFrame w witnessSuffix ∧
      input = encodeFrame (payload input.bits) inputSuffix ∧
      ∀ fuel, Source284Relative.run
        (Source284OffsetTagged.description (19+(80+(7+(210+states))))
          (Source284BothFrames.table continuation))
        (Source284Relative.initial certificate (pairTape (List.replicate limit false) input))
        (Source284BothFrames.time limit w input+fuel) =
      lift 528 (Source284Relative.run (encode states continuation 1)
        ⟨2*(4*(4^(limit+1)*(2*encodeFrame w (8*((witnessSuffix/4)/4)+1)))+1),
          encodeFrame (payload input.bits) (2*(inputSuffix/4)+1),active 0⟩ fuel) := by
  obtain ⟨x,inputSuffix,hinput⟩ := Source284Parser.encodeFrame_surjective input
  have hx : payload input.bits = x := by
    rw [← hinput]
    exact Source284NormalizedWindow.payload_encodeFrame x inputSuffix
  have hlen : Source284Parser.length input = x.length := by
    rw [← hinput]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  have hnorm := Source284ScratchNormalizePipeline.closed states continuation hn hv
  obtain ⟨ws,hcert,hr⟩ := Source284OffsetRevealInput.decoded_reveal_then
    (210+states) (Source284ScratchNormalizePipeline.table continuation)
    limit certificate input w (by omega) hnorm hdec
  refine ⟨ws,inputSuffix,hcert,by simpa [hx] using hinput.symm,?_⟩
  intro fuel
  let wf := encodeFrame w (8*((ws/4)/4)+1)
  let saved := 4*(4^(limit+1)*(2*wf))+1
  have hdesc : encode (210+states) (Source284ScratchNormalizePipeline.table continuation) 1 =
      Source284ScratchNormalizePipeline.description states continuation := by
    unfold Source284ScratchNormalizePipeline.description Source284ScratchFlipPipeline.description
    rw [show 142+(68+states) = 210+states by omega]
    rfl
  have hrun := hr (Source284ScratchNormalizePipeline.totalCost x.length+fuel)
  change Source284Relative.run _ _ _ = lift 318
    (Source284Relative.run (encode (210+states) (Source284ScratchNormalizePipeline.table continuation) 1)
      (Source284Relative.initial input saved) (Source284ScratchNormalizePipeline.totalCost x.length+fuel)) at hrun
  have hafter : Source284Relative.run (Source284ScratchNormalizePipeline.description states continuation)
      (Source284Relative.initial input saved) (Source284ScratchNormalizePipeline.totalCost x.length+fuel) =
      lift 210 (Source284Relative.run (encode states continuation 1)
        ⟨2*saved,encodeFrame x (2*(inputSuffix/4)+1),active 0⟩ fuel) := by
    rw [← hinput]
    exact normalize_after states continuation x inputSuffix saved fuel hn hv
  rw [hdesc,hafter,Source284SourceRelocation.lift_add] at hrun
  have htime : Source284BothFrames.time limit w input+fuel =
      4+(Source284PayloadSentinelPipeline.totalCost w.length+
        (Source284OffsetMatch.compareCost w.length+(1+
          ((1+((4*(limit+1)+6)+(4*w.length+12)))+
            (10*w.length+21+((3+(2*(limit+1)+3))+
              (Source284ScratchNormalizePipeline.totalCost x.length+fuel))))))) := by
    simp only [Source284BothFrames.time,hlen]
    omega
  rw [htime,hx]
  exact hrun

/-- A valid tagged certificate supplies the original-cutoff hypothesis for
the explicit quadratic preparation bound. -/
theorem decoded_time_bound (limit certificate input : Nat) (w : List Bool)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    Source284BothFrames.time limit w input ≤ 6*limit*limit+70*limit+
      2*Source284Parser.length input*Source284Parser.length input+
      28*Source284Parser.length input+148 :=
  Source284BothFrames.time_bound limit w input
    (Source284TaggedWitnessCodec.decode_length limit certificate w hdec)

namespace Fixtures

/-- The empty-input, zero-bound setup is a real positive finite prefix. -/
example : Source284BothFrames.time 0 [] 0 = 148 := by decide +kernel

end Fixtures

end Shared.Beeping.NPcoNP.Source284BothFramesContinue
