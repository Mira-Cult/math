import Shared.Beeping.NPcoNP.Source284FramedSerializeCost

/-! A uniform fixed-coefficient runway for the serializer under a linear
witness-length and quadratic observation-radius hypothesis. General
polynomial witness cutoffs remain a separate obligation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284FramedSerializeRunway

open Shared.Beeping.NPcoNP.Source284FramedSerializeTable
open Shared.Beeping.NPcoNP.Source284FramedSerialize
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros)

/-- A deliberately coarse fixed coefficient; width is fixed by the codec. -/
def coefficient (width radiusCoefficient : Nat) : Nat :=
  2000*width*width+4867*width+4846+radiusCoefficient

theorem serial_quadratic {width : Nat} (enc : Codec width) (x w : List Bool)
    (hx : 1 ≤ x.length) (hw : w.length ≤ x.length) :
    serialClock enc x w ≤ (2000*width*width+4864*width+4845)*(x.length*x.length) := by
  let n := x.length
  let m := 2*x.length+2*w.length+5
  let d := width*(m+1)
  have hn : 1 ≤ n := hx
  have hm : m ≤ 9*n := by dsimp [m,n]; omega
  have hm1 : m+1 ≤ 10*n := by omega
  have hnn : n ≤ n*n := by nlinarith
  have hwidth : width ≤ width*n := by nlinarith
  have hmul : m*(1+width) ≤ 9*n*(1+width) := Nat.mul_le_mul_right _ hm
  have hfirst : 16*(width+m*(1+width))+16*width+31 ≤ (176*width+175)*n := by nlinarith
  have hfirstProd := Nat.mul_le_mul hm hfirst
  have hsecondMul : (m+1)*(width+1) ≤ 10*n*(width+1) := Nat.mul_le_mul_right _ hm1
  have hsecond : 7*width+30*((m+1)*(width+1))+26 ≤ (307*width+326)*n := by nlinarith
  have hsecondProd := Nat.mul_le_mul hm1 hsecond
  have hd : d ≤ 10*width*n := by
    dsimp [d]
    have h := Nat.mul_le_mul_left width hm1
    nlinarith
  have hthird : 20*d+21 ≤ (200*width+21)*n := by nlinarith
  have hthirdProd := Nat.mul_le_mul hd hthird
  have hc := Source284FramedSerializeCost.serialClock_bound enc x w
  change serialClock enc x w ≤ m*(16*(width+m*(1+width))+16*width+31)+2+
    (m+1)*(7*width+30*((m+1)*(width+1))+26)+d*(20*d+21)+8 at hc
  dsimp [n] at *
  nlinarith

/-- The coefficient depends only on the fixed codec width and the fixed
radius coefficient, never on the particular tested input or witness. -/
theorem uniform_fit {width : Nat} (enc : Codec width) (r : Nat) (x w : List Bool) (radius : Nat)
    (hx : 1 ≤ x.length) (hw : w.length ≤ x.length)
    (hr : radius ≤ r*(x.length*x.length)) :
    (word enc).length+(radius+serialClock enc x w) ≤
      firstZeros (coefficient width r) x.length+2*x.length+4 := by
  have hs := serial_quadratic enc x w hx hw
  have hlen := Source284TaggedMarkerSeed.word_length enc
  change (word enc).length = 1+3*width at hlen
  have hn : 1 ≤ x.length*x.length := by nlinarith
  have hword : 1+3*width ≤ (1+3*width)*(x.length*x.length) := by nlinarith
  unfold firstZeros coefficient
  nlinarith

/-- For positive-length inputs and witnesses no longer than the input, one
fixed source table per codec and radius coefficient reaches the serializer's
output window. The original tagged certificate decoding premise is retained. -/
theorem uniform_all_inputs {width : Nat} (enc : Codec width) (r limit input certificate : Nat)
    (w : List Bool) (radius : Nat)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w)
    (hx : 1 ≤ Source284Parser.length input)
    (hw : w.length ≤ Source284Parser.length input)
    (hr : radius ≤ r*(Source284Parser.length input*Source284Parser.length input)) :
    ∃ inputSuffix witnessSuffix rev,
      input=Source284Parser.encodeFrame (Source284RawParse.payload input.bits) inputSuffix ∧
      certificate=4*Source284Parser.encodeFrame w witnessSuffix ∧
      Source284Relative.Window radius
        (Source284Relative.run (sourceDescription enc (coefficient width r))
          (Source284Relative.initial input certificate)
          (sourceTime enc (coefficient width r) (Source284RawParse.payload input.bits) w))
        (Source284SourceRelocation.lift (1286+220*(coefficient width r))
          (target enc (Source284RawParse.payload input.bits) w
            (inputList (coefficient width r) (Source284RawParse.payload input.bits) inputSuffix) rev)) := by
  have hlen : (Source284RawParse.payload input.bits).length = Source284Parser.length input := by
    have h := Source284RawParse.parse_length input.bits
    rw [Shared.Codes.BinaryAdditionCanonical.value_bits] at h
    exact h.symm
  apply Source284FramedSerializeCoverage.all_inputs_serialize_window enc (coefficient width r)
    limit input certificate w radius hdec
  have hf := uniform_fit enc r (Source284RawParse.payload input.bits) w radius
    (by simpa [hlen] using hx) (by simpa [hlen] using hw) (by simpa [hlen] using hr)
  simpa [hlen] using hf

end Shared.Beeping.NPcoNP.Source284FramedSerializeRunway
