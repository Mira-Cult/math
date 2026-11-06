import Shared.Beeping.NPcoNP.Source284GuardedSourceTerminal
import Shared.Beeping.NPcoNP.Source284FramedSerializeCost

/-! Polynomial upper bounds for the joined verifier's output cleanup and the
source serializer. This does not construct the required polynomial runway. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284VerifierPolynomialBudget

open Turing Shared.ComplexityBridge
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.Beeping.NPcoNP.Source284FramedEncoderTable (Codec)

noncomputable def cleanupPolynomial (width : Nat) : Polynomial Nat :=
  let n := Polynomial.X
  ((Polynomial.C width+7)+(n*(Polynomial.C width+7)+(Polynomial.C width+5)))+
    (2+((Polynomial.C width+4)+((n+1)*((10*Polynomial.C width+36)*n+
      19*Polynomial.C width+69)+2*n)))+
    2+(3*n+5+(n*(20*n+21)+6))

theorem cleanupPolynomial_eval (width n : Nat) :
    (cleanupPolynomial width).eval n =
      ((width+7)+(n*(width+7)+(width+5)))+
      (2+((width+4)+((n+1)*((10*width+36)*n+19*width+69)+2*n)))+
      2+(3*n+5+(n*(20*n+21)+6)) := by
  simp [cleanupPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]

/-- For nonempty output, the actual cleanup cost has one polynomial bound in
the output length. The codec width is fixed in the program. -/
theorem cleanup_bound (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool)
    (bits : List Bool) (first : Bool) (bs : List Bool) (hrev : bits.reverse = first::bs) :
    TM2OutputProtectedRaw.cost tm enc out bits bs ≤ (cleanupPolynomial width).eval bits.length := by
  have hbs : bs.length ≤ bits.length := by
    have h := congrArg List.length hrev
    simp only [List.length_reverse,List.length_cons] at h
    omega
  have h := TM2OutputProtectedRaw.cost_bound tm enc out bits first bs hrev
  rw [cleanupPolynomial_eval]
  unfold TM2OutputProtectedPipeline.writerCost at h
  apply le_trans h
  gcongr

noncomputable def serializerPolynomial (width : Nat) : Polynomial Nat :=
  let m := 2*Polynomial.X+5
  let d := Polynomial.C width*(m+1)
  m*(16*(Polynomial.C width+m*(1+Polynomial.C width))+16*Polynomial.C width+31)+2+
    (m+1)*(7*Polynomial.C width+30*((m+1)*(Polynomial.C width+1))+26)+
    d*(20*d+21)+8

theorem serializerPolynomial_eval (width n : Nat) :
    let m := 2*n+5
    let d := width*(m+1)
    (serializerPolynomial width).eval n =
      m*(16*(width+m*(1+width))+16*width+31)+2+
      (m+1)*(7*width+30*((m+1)*(width+1))+26)+d*(20*d+21)+8 := by
  simp only [serializerPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]

/-- The complete source serializer, including its two-step verifier handoff,
is bounded in the sum of input and witness lengths plus verifier fuel. -/
theorem serializer_bound {width : Nat} (enc : Codec width) (x w : List Bool) (fuel : Nat) :
    Source284FramedEncoder.serialClock enc x w fuel ≤
      (serializerPolynomial width).eval (x.length+w.length)+2+fuel := by
  have h := Source284FramedSerializeCost.serialClock_bound enc x w
  have heval := serializerPolynomial_eval width (x.length+w.length)
  dsimp only at heval h
  have hm : 2*(x.length+w.length)+5 = 2*x.length+2*w.length+5 := by omega
  rw [hm] at heval
  have hs : Source284FramedEncoder.serialClock enc x w fuel =
      Source284FramedSerialize.serialClock enc x w+2+fuel := by
    simp only [Source284FramedEncoder.serialClock,Source284FramedSerialize.serialClock,
      Source284FramedEncoderTable.zero,Source284FramedEncoderTable.one,
      Source284FramedEncoderTable.kept,Source284FramedSerializeTable.zero,
      Source284FramedSerializeTable.one,Source284FramedSerializeTable.kept]
    omega
  rw [hs,heval]
  omega

end Shared.Beeping.NPcoNP.Source284VerifierPolynomialBudget
