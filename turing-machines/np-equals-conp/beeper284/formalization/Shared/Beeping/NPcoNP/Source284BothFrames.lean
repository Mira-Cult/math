import Shared.Beeping.NPcoNP.Source284OffsetRevealInput
import Shared.Beeping.NPcoNP.Source284NormalizedWindow

/-! Paid source preparation of both the decoded witness frame and the parsed
input frame. They remain on opposite tape halves; no pair loader is assumed. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284BothFrames

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284RawParse (payload)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284OffsetFrameAdapter.table
    (Source284OffsetRevealInput.table (Source284ScratchNormalizePipeline.table continuation))

def time (limit : Nat) (w : List Bool) (input : Nat) : Nat :=
  4+(Source284PayloadSentinelPipeline.totalCost w.length+
    (Source284OffsetMatch.compareCost w.length+(1+
      ((1+((4*(limit+1)+6)+(4*w.length+12)))+
        (10*w.length+21+((3+(2*(limit+1)+3))+
          Source284ScratchNormalizePipeline.totalCost (Source284Parser.length input)))))))

/-- The whole paid preparation is quadratically bounded by the original
witness cutoff and the parsed input length, independently of both suffixes. -/
theorem time_bound (limit : Nat) (w : List Bool) (input : Nat) (hw : w.length ≤ limit) :
    time limit w input ≤ 6*limit*limit+70*limit+
      2*Source284Parser.length input*Source284Parser.length input+
      28*Source284Parser.length input+148 := by
  unfold time
  rw [Source284PayloadSentinelPipeline.totalCost_formula,
    Source284ScratchNormalizePipeline.totalCost_formula]
  unfold Source284OffsetMatch.compareCost
  have hsq : w.length*w.length ≤ limit*limit := Nat.mul_le_mul hw hw
  nlinarith

/-- The saved witness half still exposes the exact canonical frame on its
finite low window after the explicitly known displacement is undone. -/
theorem saved_witness_window (limit : Nat) (w : List Bool) (tail : Nat) :
    Source284CanonicalPairWindow.window (2*w.length+2)
      ((4*(4^(limit+1)*(2*encodeFrame w (8*tail+1)))+1)/4^(limit+2)/2) =
      Source284Parser.frameBits w [true] := by
  have he : limit+2 = (limit+1)+1 := by omega
  rw [he,Source284OffsetRevealInput.reveal_frame_recover]
  simpa using Source284OffsetFrameAdapter.frame_low_bits w tail

/-- The record count accounts for both new finite prefixes; the supplied
continuation remains a separately encoded finite table. -/
theorem table_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (19+(80+(7+(210+states)))) (table continuation) := by
  have h := Source284ScratchNormalizePipeline.closed states continuation hn hv
  exact Source284OffsetFrameAdapter.closed (7+(210+states))
    (Source284OffsetRevealInput.table (Source284ScratchNormalizePipeline.table continuation))
    (by omega) (Source284OffsetRevealInput.closed (210+states)
      (Source284ScratchNormalizePipeline.table continuation) (by omega) h)

/-- For every successfully decoded witness, the actual source table reaches
both framed components in finite input- and witness-length cost. The complete
witness frame and all suffix data remain recoverable on the opposite half. -/
theorem both_frames (states : Nat) (continuation : Nat → Bool → Row)
    (limit certificate input : Nat) (w : List Bool)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    ∃ witnessSuffix inputSuffix,
      certificate = 4*encodeFrame w witnessSuffix ∧
      input = encodeFrame (payload input.bits) inputSuffix ∧
      let wf := encodeFrame w (8*((witnessSuffix/4)/4)+1)
      let saved := 4*(4^(limit+1)*(2*wf))+1
      Source284Relative.run (Source284OffsetTagged.description (19+(80+(7+(210+states)))) (table continuation))
        (Source284Relative.initial certificate (pairTape (List.replicate limit false) input))
        (time limit w input) =
          ⟨2*saved,encodeFrame (payload input.bits) (2*(inputSuffix/4)+1),active 528⟩ ∧
      saved / 4^(limit+2) = 2*wf ∧
      Source284CanonicalPairWindow.window (2*(payload input.bits).length+2)
        (encodeFrame (payload input.bits) (2*(inputSuffix/4)+1)) =
          Source284Parser.frameBits (payload input.bits) [true] := by
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
  dsimp only
  let wf := encodeFrame w (8*((ws/4)/4)+1)
  let saved := 4*(4^(limit+1)*(2*wf))+1
  have hdesc : encode (210+states) (Source284ScratchNormalizePipeline.table continuation) 1 =
      Source284ScratchNormalizePipeline.description states continuation := by
    unfold Source284ScratchNormalizePipeline.description Source284ScratchFlipPipeline.description
    rw [show 142+(68+states) = 210+states by omega]
    rfl
  have hrun := hr (Source284ScratchNormalizePipeline.totalCost x.length)
  change Source284Relative.run _ _ _ = lift 318
    (Source284Relative.run (encode (210+states) (Source284ScratchNormalizePipeline.table continuation) 1)
      (Source284Relative.initial input saved) (Source284ScratchNormalizePipeline.totalCost x.length)) at hrun
  have hpipeline : Source284Relative.run (Source284ScratchNormalizePipeline.description states continuation)
      (Source284Relative.initial input saved) (Source284ScratchNormalizePipeline.totalCost x.length) =
      ⟨2*saved,encodeFrame x (2*(inputSuffix/4)+1),active 210⟩ := by
    rw [← hinput]
    exact Source284ScratchNormalizePipeline.source_pipeline states continuation x saved inputSuffix hn hv
  rw [hdesc,hpipeline,Source284SourceRelocation.lift_active] at hrun
  have htime : time limit w input =
      4+(Source284PayloadSentinelPipeline.totalCost w.length+
        (Source284OffsetMatch.compareCost w.length+(1+
          ((1+((4*(limit+1)+6)+(4*w.length+12)))+
            (10*w.length+21+((3+(2*(limit+1)+3))+
              Source284ScratchNormalizePipeline.totalCost x.length)))))) := by simp [time,hlen]
  refine ⟨?_,?_,?_⟩
  · rw [htime,hx]
    exact hrun
  · have he : limit+2 = (limit+1)+1 := by omega
    rw [he]
    exact Source284OffsetRevealInput.reveal_frame_recover (limit+1) wf
  · rw [hx]
    have hh := Source284NormalizedWindow.normalized_mod x (inputSuffix/4)
    apply Source284CanonicalPairWindow.same_length_value_injective
    · rw [Source284CanonicalPairWindow.window_length,Source284WitnessWindow.frame_length]
    · rw [Source284CanonicalPairWindow.window_value]
      have hp : 2^(2*x.length+2) = 4^(x.length+1) := by
        have ht : 2*x.length+2 = 2*(x.length+1) := by omega
        rw [ht,Nat.pow_mul]
      rw [hp,hh]
      simpa [Shared.Codes.BitNumeralCompare.value] using Source284Parser.encodeFrame_eq_value x [true]

end Shared.Beeping.NPcoNP.Source284BothFrames
