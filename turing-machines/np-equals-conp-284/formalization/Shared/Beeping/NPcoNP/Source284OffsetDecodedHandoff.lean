import Shared.Beeping.NPcoNP.Source284OffsetExactHandoff
import Shared.Beeping.NPcoNP.Source284NormalizedWindow
import Shared.Beeping.NPcoNP.Source284BitWindow

/-! Relate the exact source handoff to the decoded witness for every valid
tagged certificate, including arbitrarily high aliases. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284OffsetDecodedHandoff

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284BitWindow
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift)

/-- The marker and payload bits, together with the final zero marker,
uniquely determine the framed list, regardless of higher bits. -/
theorem frame_of_agree (w : List Bool) (suffix n : Nat)
    (h : Agree (2*w.length+1) (encodeFrame w suffix) n) :
    ∃ tail, n = encodeFrame w tail := by
  induction w generalizing n with
  | nil =>
    have he := agree_head (k := 0) (by simpa using h)
    have hn : n%2 = 0 := by simpa [encodeFrame] using he.symm
    refine ⟨n/2, ?_⟩
    simp only [encodeFrame]
    omega
  | cons b bs ih =>
    have ha : Agree (2*bs.length+3) (encodeFrame (b::bs) suffix) n := by
      change Agree (2*(bs.length+1)+1) (encodeFrame (b::bs) suffix) n at h
      rw [show 2*(bs.length+1)+1 = 2*bs.length+3 by omega] at h
      exact h
    have h0 := agree_head ha
    have h1 := agree_head (agree_tail ha)
    have h2 := agree_tail (agree_tail ha)
    have hn0 : n%2 = 1 := by
      cases b <;> simp [encodeFrame] at h0 <;> omega
    have hn1 : (n/2)%2 = (if b then 1 else 0) := by
      cases b <;> simp [encodeFrame] at h1 ⊢ <;> omega
    have hf : encodeFrame (b::bs) suffix / 2 / 2 = encodeFrame bs suffix := by
      cases b <;> simp [encodeFrame] <;> omega
    rw [hf] at h2
    obtain ⟨tail, ht⟩ := ih (n/2/2) (by simpa using h2)
    refine ⟨tail, ?_⟩
    have hdiv : n/4 = n/2/2 := by omega
    simp only [encodeFrame]
    cases b <;> simp at hn1 ⊢ <;> omega

/-- The fixed low window contains the complete frame for a within-bound
witness. High suffixes never change the decoded witness. -/
theorem raw_decode_frame (limit : Nat) (w : List Bool) (suffix : Nat)
    (hw : w.length ≤ limit) :
    Source284WitnessWindow.decode limit (encodeFrame w suffix) = some w := by
  let width := Source284WitnessWindow.width limit
  let n := encodeFrame w suffix % 2^width
  have hle : 2*w.length+1 ≤ width := by dsimp [width,Source284WitnessWindow.width]; omega
  have ha : Agree (2*w.length+1) (encodeFrame w suffix) n :=
    agree_mono hle (agree_truncate width (encodeFrame w suffix))
  obtain ⟨tail, ht⟩ := frame_of_agree w suffix n ha
  have hp : Source284RawParse.payload n.bits = w := by
    rw [ht]
    exact Source284NormalizedWindow.payload_encodeFrame w tail
  unfold Source284WitnessWindow.decode
  change (if (Source284RawParse.payload n.bits).length ≤ limit then
    some (Source284RawParse.payload n.bits) else none) = some w
  rw [hp]
  simp [hw]

theorem tagged_decode_frame (limit : Nat) (w : List Bool) (suffix : Nat)
    (hw : w.length ≤ limit) :
    Source284TaggedWitnessCodec.decode limit (4*encodeFrame w suffix) = some w := by
  simpa [Source284TaggedWitnessCodec.decode] using raw_decode_frame limit w suffix hw

/-- For every successfully decoded certificate, the verifier is reached on
the tape for that very witness, not merely for an existentially unrelated
frame. The exact retained suffix is exhibited and not assumed erased. -/
theorem decoded_verifier_exact (states : Nat) (verifier : Nat → Bool → Source284TableEncode.Row)
    (limit certificate otherHalf : Nat) (w : List Bool)
    (hn : 0 < states) (hv : Source284TableRun.Closed states verifier)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    ∃ suffix, certificate = 4*encodeFrame w suffix ∧
      ∀ fuel, Source284Relative.run (Source284OffsetTagged.description states verifier)
        (Source284Relative.initial certificate (pairTape (List.replicate limit false) otherHalf))
        (4+(Source284PayloadSentinelPipeline.totalCost w.length+
          (Source284OffsetMatch.compareCost w.length+(1+fuel)))) =
      lift 212 (Source284Relative.run (encode states verifier 1)
        ⟨2*zeros w (flipped [false] ((suffix/4)/4)),
          pairTape (Source284OffsetExactHandoff.boundTokens limit w) otherHalf,active 0⟩ fuel) := by
  have htag : certificate%4 = 0 := by
    by_contra h
    simp [Source284TaggedWitnessCodec.decode,h] at hdec
  obtain ⟨v,suffix,hframe⟩ := Source284Parser.encodeFrame_surjective (certificate/4)
  have hcert : certificate = 4*encodeFrame v suffix := by rw [hframe]; omega
  have hvalid : Source284TaggedWitnessCodec.decode limit (4*encodeFrame v suffix) ≠ none := by
    rw [← hcert,hdec]
    simp
  have hvlen : v.length ≤ limit := by
    by_contra h
    apply hvalid
    exact (Source284PreparedCutoff.tagged_decode_none_iff limit v suffix).mpr (by omega)
  have hdecoded := tagged_decode_frame limit v suffix hvlen
  rw [← hcert,hdec] at hdecoded
  have heq : w = v := Option.some.inj hdecoded
  subst v
  refine ⟨suffix,hcert,?_⟩
  intro fuel
  rw [hcert]
  exact Source284OffsetExactHandoff.source_verifier_exact states verifier limit w suffix otherHalf fuel hn hv hvlen

namespace Fixtures

/-- A lone marker uses the virtual zero payload bit. -/
example : Source284TaggedWitnessCodec.decode 1 4 = some [false] := by decide +kernel

/-- High suffixes preserve the decoded nonempty witness. -/
example : Source284TaggedWitnessCodec.decode 1 (4*encodeFrame [true] 12345) = some [true] :=
  tagged_decode_frame 1 [true] 12345 (by decide)

end Fixtures

end Shared.Beeping.NPcoNP.Source284OffsetDecodedHandoff
