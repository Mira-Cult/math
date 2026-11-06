import Shared.Beeping.NPcoNP.Source284OffsetFrameAdapter
import Shared.Beeping.NPcoNP.Source284RawParseTM2
import Shared.ComplexityBridge.TM2Serialize

/-! A genuine canonical-TM2 polynomial-time conversion of a bounded witness
frame, once the frame window and the first component have been loaded as
canonical inputs. This does not implement the source-tape window loader. -/
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284CanonicalFrameTM2

open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame frameBits)
open Shared.Beeping.NPcoNP.Source284RawParse (payload)

/-- Interpret a raw framed witness and serialize the exact Google canonical
pair. Malformed frames use the total source parser's virtual-zero convention. -/
def pack (p : List Bool × List Bool) : List Bool :=
  BitstringEncoding.bitEncode (p.1,payload p.2)

/-- The conversion has a concrete canonical TM2 polynomial-time witness:
project the components, run the proved finite parser, form the pair, and
serialize its library encoding. The input is the canonical encoding of the
pair of lists, not a free tape window. -/
theorem pack_isPolyTime : ComplexityTheory.IsPolyTime pack := by
  let first : List Bool × List Bool → List Bool := fun p => p.1
  let second : List Bool × List Bool → List Bool := fun p => p.2
  have hfirst : ComplexityTheory.IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hsecond : ComplexityTheory.IsPolyTime second := TM2GuardAllStep.second_isPolyTime
  have hpayload : ComplexityTheory.IsPolyTime (fun p => payload (second p)) :=
    TM2Compose.isPolyTime_comp second payload hsecond Source284RawParseTM2.payload_isPolyTime
  have hpair : ComplexityTheory.IsPolyTime (fun p => (first p,payload (second p))) :=
    TM2GuardAllStep.pair_isPolyTime first (fun p => payload (second p)) hfirst hpayload
  have hserialize : ComplexityTheory.IsPolyTime
      (BitstringEncoding.bitEncode : (List Bool × List Bool) → List Bool) := TM2Serialize.isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p => (first p,payload (second p)))
    (BitstringEncoding.bitEncode : (List Bool × List Bool) → List Bool) hpair hserialize

/-- Full frames have the original witness, including trailing false bits. -/
theorem pack_frame (x w suffix : List Bool) :
    pack (x,frameBits w suffix) = BitstringEncoding.bitEncode (x,w) := by
  unfold pack
  have hp : payload (frameBits w suffix) = w := by
    induction w with
    | nil => simp [frameBits,payload]
    | cons b bs ih => simp [frameBits,payload,ih]
  rw [hp]

/-- The exact finite low window reached by the checked source adapter is a
valid input to the canonical TM2 conversion, independent of its high suffix. -/
theorem pack_source_window (x w : List Bool) (tail : Nat) :
    pack (x,Source284CanonicalPairWindow.window (2*w.length+2)
      (encodeFrame w (8*tail+1))) = BitstringEncoding.bitEncode (x,w) := by
  rw [Source284OffsetFrameAdapter.frame_low_bits]
  exact pack_frame x w [true]

/-- The output has the canonical, not framed, bit length. -/
theorem output_length (x w : List Bool) (tail : Nat) :
    (pack (x,Source284CanonicalPairWindow.window (2*w.length+2)
      (encodeFrame w (8*tail+1)))).length = 6*x.length+1+3*w.length := by
  rw [pack_source_window]
  exact Shared.ComplexityBridge.bitstring_pair_encoded_length x w

/-- The paid source prefix really reaches a configuration whose bounded
right-hand window gives the exact library pair after `pack`. This links the
mathematical window to execution; it does not compile `pack` into that source
table or provide the still-missing input/window loader. -/
theorem decoded_source_pack (states : Nat)
    (continuation : Nat → Bool → Source284TableEncode.Row)
    (limit certificate otherHalf : Nat) (x w : List Bool)
    (hn : 0 < states) (hv : Source284TableRun.Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    ∃ suffix,
      certificate = 4*encodeFrame w suffix ∧
      Source284Relative.run
        (Source284OffsetTagged.description (19+(80+states))
          (Source284OffsetFrameAdapter.table continuation))
        (Source284Relative.initial certificate
          (Source284UnaryPairScanner.pairTape (List.replicate limit false) otherHalf))
        (4+(Source284PayloadSentinelPipeline.totalCost w.length+
          (Source284OffsetMatch.compareCost w.length+(1+
            ((1+((4*(limit+1)+6)+(4*w.length+12)))+(10*w.length+21)))))) =
      ⟨2*Source284UnaryPairScanner.pairTape (List.replicate (limit+1) false) otherHalf,
        encodeFrame w (8*((suffix/4)/4)+1),Source284TableEncode.active 311⟩ ∧
      pack (x,Source284CanonicalPairWindow.window (2*w.length+2)
        (encodeFrame w (8*((suffix/4)/4)+1))) = BitstringEncoding.bitEncode (x,w) := by
  obtain ⟨suffix,hcert,_,hr⟩ := Source284OffsetFrameAdapter.decoded_frame_then
    states continuation limit certificate otherHalf w hn hv hdec
  refine ⟨suffix,hcert,?_,pack_source_window x w ((suffix/4)/4)⟩
  have hh := hr 0
  simpa [Source284Relative.run, Source284SourceRelocation.lift_active] using hh

namespace Fixtures

/-- A virtual payload zero in the source convention becomes a real false
witness bit in the canonical pair. -/
example : pack ([true],[true]) = BitstringEncoding.bitEncode ([true],[false]) := by
  rfl

example : pack ([],[false,true,true]) = BitstringEncoding.bitEncode (([] : List Bool),([] : List Bool)) := by
  rfl

end Fixtures

end Shared.Beeping.NPcoNP.Source284CanonicalFrameTM2
