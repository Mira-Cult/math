import Shared.Beeping.NPcoNP.Source284WitnessCompact
import Shared.Beeping.NPcoNP.Source284ScratchNormalize
import Shared.Beeping.NPcoNP.Source284NormalizedWindow

/-! Reframe the compacted witness with a canonical one sentinel, immediately
beside the preserved input frame. This is still a two-sided frame layout; it
does not serialize Google's pair encoding or refine the physical beeper. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284WitnessReframe

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (68+states) (Source284ScratchNormalize.table continuation) := by
  have h := Source284ScratchNormalize.closed states continuation hn hv
  convert h using 1 <;> omega

/-- The normalizer's self-delimiting return preserves every later transition. -/
theorem normalize_then (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail fuel : Nat) :
    run (Source284ScratchNormalize.table continuation)
      ⟨certificate,2*flipped w tail,some 0⟩ ((6*w.length+11)+fuel) =
    shiftConfig 68 (run continuation
      ⟨2*certificate,encodeFrame w (2*tail+1),some 0⟩ fuel) := by
  rw [run_add,Source284ScratchNormalize.normalize]
  change run (Source284ScratchNormalize.table continuation)
    (shiftConfig 36 (shiftConfig 32 ⟨2*certificate,encodeFrame w (2*tail+1),some 0⟩)) fuel = _
  rw [Source284ScratchNormalize.relocated_run,Source284ModePrefixReturn.relocated_run,
    Source284SourceRelocation.shiftConfig_add]

/-- The actual valid-certificate path ends at adjacent source frames: the
original parsed input and the complete witness, each with a one sentinel.
All normalization transitions and every later continuation step are paid. -/
theorem decoded_reframe_then (states : Nat) (continuation : Nat → Bool → Row)
    (limit certificate input : Nat) (w : List Bool)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    ∃ witnessSuffix inputSuffix,
      certificate = 4*encodeFrame w witnessSuffix ∧
      input = encodeFrame (Source284RawParse.payload input.bits) inputSuffix ∧
      ∀ fuel, Source284Relative.run
        (Source284OffsetTagged.description (19+(80+(7+(210+(10+(160+(68+states)))))))
          (Source284BothFrames.table (Source284WitnessSeek.table
            (Source284WitnessCompact.table (Source284ScratchNormalize.table continuation)))))
        (Source284Relative.initial certificate
          (Source284UnaryPairScanner.pairTape (List.replicate limit false) input))
        (Source284BothFrames.time limit w input+
          ((3+2*((limit+1)+1)+(if w = [] then 4 else 2))+
            (Source284WitnessCompact.extraCost (limit+1) w.length+((6*w.length+11)+fuel)))) =
      Source284SourceRelocation.lift 766 (Source284Relative.run (encode states continuation 1)
        ⟨2*(4*encodeFrame (Source284RawParse.payload input.bits) (2*(inputSuffix/4)+1)+1),
          encodeFrame w (2*(2^(2*((limit+1)+1))*((8*((witnessSuffix/4)/4)+1)/4))+1),active 0⟩ fuel) := by
  obtain ⟨ws,is,hcert,hinput,hr⟩ := Source284WitnessCompact.decoded_compact_then
    (68+states) (Source284ScratchNormalize.table continuation) limit certificate input w (by omega)
      (closed states continuation hn hv) hdec
  refine ⟨ws,is,hcert,hinput,?_⟩
  intro fuel
  let x := Source284RawParse.payload input.bits
  let left := 4*encodeFrame x (2*(is/4)+1)+1
  let tail := 2^(2*((limit+1)+1))*((8*((ws/4)/4)+1)/4)
  let t := 6*w.length+11
  have hr' := hr (t+fuel)
  change Source284Relative.run _ _ _ = Source284SourceRelocation.lift 698
    (Source284Relative.run (encode (68+states) (Source284ScratchNormalize.table continuation) 1)
      ⟨left,2*flipped w tail,active 0⟩ (t+fuel)) at hr'
  let c : Config := ⟨left,2*flipped w tail,some 0⟩
  have hc : Valid (68+states) c := by intro q hq; simp [c] at hq; subst q; omega
  have hv0 := run_toSource (68+states) (Source284ScratchNormalize.table continuation) 1 c
    (closed states continuation hn hv) hc (t+fuel)
  change Source284Relative.run (encode (68+states) (Source284ScratchNormalize.table continuation) 1)
    ⟨left,2*flipped w tail,active 0⟩ (t+fuel) = _ at hv0
  have hp := normalize_then continuation w left tail fuel
  change run (Source284ScratchNormalize.table continuation) c (t+fuel) = _ at hp
  rw [hv0,hp] at hr'
  let c' : Config := ⟨2*left,encodeFrame w (2*tail+1),some 0⟩
  have hc' : Valid states c' := by intro q hq; simp [c'] at hq; subst q; exact hn
  have hv1 := run_toSource states continuation 1 c' hv hc' fuel
  change Source284Relative.run (encode states continuation 1)
    ⟨2*left,encodeFrame w (2*tail+1),active 0⟩ fuel = _ at hv1
  rw [← Source284SourceRelocation.lift_toSource,Source284SourceRelocation.lift_add,← hv1] at hr'
  exact hr'

/-- The two source frames retain the same parsed input and witness as their
canonical-sentinel versions, independently of their retained high suffixes. -/
theorem frame_parses (x w : List Bool) (inputTail witnessTail : Nat) :
    Source284Parser.parse (encodeFrame x (2*inputTail+1)) = Source284Parser.parse (encodeFrame x 1) ∧
    Source284Parser.parse (encodeFrame w (2*witnessTail+1)) = Source284Parser.parse (encodeFrame w 1) :=
  ⟨Source284Parser.parse_suffix_independent x _ _,Source284Parser.parse_suffix_independent w _ _⟩

/-- The complete canonical frame windows and both decoded payload lists are
unchanged by arbitrary retained high suffix data. These are two separate
windows, not yet the canonical pair-encoded verifier window. -/
theorem frame_windows (x w : List Bool) (inputTail witnessTail : Nat) :
    encodeFrame x (2*inputTail+1) % 4^(x.length+1) = encodeFrame x 1 ∧
    encodeFrame w (2*witnessTail+1) % 4^(w.length+1) = encodeFrame w 1 ∧
    Source284RawParse.payload (encodeFrame x (2*inputTail+1)).bits = x ∧
    Source284RawParse.payload (encodeFrame w (2*witnessTail+1)).bits = w :=
  ⟨Source284NormalizedWindow.normalized_mod x inputTail,
    Source284NormalizedWindow.normalized_mod w witnessTail,
    Source284NormalizedWindow.payload_encodeFrame x _,
    Source284NormalizedWindow.payload_encodeFrame w _⟩

theorem decoded_reframe_bound (limit certificate input : Nat) (w : List Bool)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    Source284BothFrames.time limit w input+
      ((3+2*((limit+1)+1)+(if w = [] then 4 else 2))+
        (Source284WitnessCompact.extraCost (limit+1) w.length+(6*w.length+11))) ≤
      24*limit*limit+154*limit+
        2*Source284Parser.length input*Source284Parser.length input+
        28*Source284Parser.length input+240 := by
  have h0 := Source284WitnessCompact.decoded_compact_bound limit certificate input w hdec
  have h1 := Source284TaggedWitnessCodec.decode_length limit certificate w hdec
  omega

namespace Fixtures
example (continuation : Nat → Bool → Row) :
    run (Source284ScratchNormalize.table continuation) ⟨7,150,some 0⟩ 23 =
      ⟨14,103,some 68⟩ := by
  simpa [flipped,encodeFrame,bit] using Source284ScratchNormalize.normalize continuation [true,false] 7 1
end Fixtures
end Shared.Beeping.NPcoNP.Source284WitnessReframe
