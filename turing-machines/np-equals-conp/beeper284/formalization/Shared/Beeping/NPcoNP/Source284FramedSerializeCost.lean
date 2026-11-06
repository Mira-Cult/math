import Shared.Beeping.NPcoNP.Source284FramedSerializeCoverage

/-! Explicit bit-size and step bounds for the fixed-width serializer stage. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284FramedSerializeCost

open Shared.Beeping.NPcoNP.Source284FramedSerializeTable
open Shared.Beeping.NPcoNP.Source284FramedSerialize
open Shared.Beeping.NPcoNP.Source284FramedSerializeCoverage

theorem remaining_length (x w : List Bool) :
    (remaining x w).length = 2*x.length+2*w.length+5 := by
  have hjoin := congrArg List.length (Source284JoinedPrefixScan.joined_eq_body x w)
  simp only [List.length_append,List.length_singleton,Source284JoinedFrames.joined_length] at hjoin
  have hbody := congrArg List.length (body_reverse x w)
  simp only [List.length_reverse,List.length_cons] at hbody
  simp only [remaining,List.length_append,List.length_cons,List.length_nil]
  omega

set_option backward.isDefEq.respectTransparency false in
theorem output_length {width : Nat} (enc : Codec width) (x w : List Bool) :
    (out enc x w).length = width*(2*x.length+2*w.length+6) := by
  rw [serialized_words,Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits_length,
    Source284JoinedFrames.joined_length]
  have h : max (2*x.length+2*w.length+6) 1 = 2*x.length+2*w.length+6 := by omega
  rw [h]

/-- An explicit polynomial in both input lengths for fixed codec width. -/
theorem serialClock_bound {width : Nat} (enc : Codec width) (x w : List Bool) :
    let m := 2*x.length+2*w.length+5
    let d := width*(m+1)
    serialClock enc x w ≤
      m*(16*(width+m*(1+width))+16*width+31)+2+
      (m+1)*(7*width+30*((m+1)*(width+1))+26)+d*(20*d+21)+8 := by
  dsimp only
  have hs := Source284SerializerStripWindow.combined_cost_bound enc (remaining x w)
  have hu := Shared.Codes.FiniteProgramUntag.cost_bound (out enc x w).reverse
  rw [List.length_reverse,output_length] at hu
  rw [remaining_length] at hs
  have he : width*(2*x.length+2*w.length+6) = width*(2*x.length+2*w.length+5+1) := by congr 1 <;> omega
  rw [he] at hu
  unfold serialClock
  dsimp [zero,one,kept]
  omega

end Shared.Beeping.NPcoNP.Source284FramedSerializeCost
