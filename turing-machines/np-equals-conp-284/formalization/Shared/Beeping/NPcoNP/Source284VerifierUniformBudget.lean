import Shared.Beeping.NPcoNP.Source284VerifierPolynomialBudget

/-! A single explicit polynomial bounds both source runway demands for a
fixed verifier and a fixed polynomial witness cutoff. The physical runway
generator remains an independent obligation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284VerifierUniformBudget

open Turing Shared.ComplexityBridge
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.Beeping.NPcoNP.Source284VerifierPolynomialBudget
open Shared.Beeping.NPcoNP.Source284JoinedFrames
open Shared.Beeping.NPcoNP.Source284FramedEncoderTable (word)
open Shared.Beeping.NPcoNP.Source284FramedEncoder (serialClock)

noncomputable def totalSize (witness : Polynomial Nat) : Polynomial Nat := Polynomial.X+witness
noncomputable def joinedSize (witness : Polynomial Nat) : Polynomial Nat := 2*totalSize witness+6
noncomputable def packedSize (witness : Polynomial Nat) : Polynomial Nat := 12*totalSize witness+37

noncomputable def runtimePolynomial (width : Nat) (simulation verifier witness : Polynomial Nat) : Polynomial Nat :=
  simulation.comp (joinedSize witness) + (cleanupPolynomial width).comp (packedSize witness) +
    verifier.comp (packedSize witness) + 4

/-- The protected codec has three additional bits per symbol. -/
noncomputable def runwayPolynomial (width : Nat) (simulation verifier witness : Polynomial Nat) : Polynomial Nat :=
  runtimePolynomial width simulation verifier witness +
    (serializerPolynomial (width+3)).comp (totalSize witness) + Polynomial.C (3*(width+3)+5)

theorem runtimePolynomial_eval (width n : Nat) (simulation verifier witness : Polynomial Nat) :
    (runtimePolynomial width simulation verifier witness).eval n =
      simulation.eval (2*(n+witness.eval n)+6) +
      (cleanupPolynomial width).eval (12*(n+witness.eval n)+37) +
      verifier.eval (12*(n+witness.eval n)+37)+4 := by
  simp [runtimePolynomial,joinedSize,packedSize,totalSize,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_X]

theorem runwayPolynomial_eval (width n : Nat) (simulation verifier witness : Polynomial Nat) :
    (runwayPolynomial width simulation verifier witness).eval n =
      (runtimePolynomial width simulation verifier witness).eval n +
      (serializerPolynomial (width+3)).eval (n+witness.eval n) + (3*(width+3)+5) := by
  simp [runwayPolynomial,totalSize,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_X]

/-- Both exact low-zero-window demands used by the source theorem are
dominated by one polynomial in input length whenever the witness has the
specified polynomial length bound. -/
theorem demands_bounded {width : Nat}
    (enc : Alphabet Source284JoinedHaltingEncoder.machine → List.Vector Bool width)
    (simulation verifier witness : Polynomial Nat) (x w : List Bool)
    (first : Bool) (bs : List Bool) (d fuel : Nat)
    (hw : w.length ≤ witness.eval x.length)
    (hrev : (BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool))).reverse = first::bs)
    (hd : d ≤ simulation.eval (joinedBits x w).length)
    (hfuel : fuel < d+2+(TM2OutputProtectedRaw.cost Source284JoinedHaltingEncoder.machine enc
      (Equiv.refl Bool) (BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool))) bs+2+
      verifier.eval (BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool))).length)) :
    fuel ≤ (runtimePolynomial width simulation verifier witness).eval x.length ∧
    1+fuel-(2*(inputBits Source284JoinedRawEncodeTM2.machine
      (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) (joinedBits x w)).length+3) ≤
        (runwayPolynomial width simulation verifier witness).eval x.length ∧
    (word (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc)).length+
      (1+serialClock (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) x w fuel) ≤
        (runwayPolynomial width simulation verifier witness).eval x.length := by
  let bits := BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool))
  let n := x.length
  let s := n+witness.eval n
  have hsize : x.length+w.length ≤ s := by dsimp [s,n]; omega
  have hjoin : (joinedBits x w).length ≤ 2*s+6 := by
    rw [joined_length]
    omega
  have hbits : bits.length ≤ 12*s+37 := by
    dsimp [bits]
    rw [Source284JoinedDecodeTM2.canonical_joined_length]
    omega
  have hsim := TM2Compose.polynomial_eval_mono simulation hjoin
  have hclean := cleanup_bound Source284JoinedHaltingEncoder.machine enc (Equiv.refl Bool) bits first bs hrev
  have hclean' := TM2Compose.polynomial_eval_mono (cleanupPolynomial width) hbits
  have hver := TM2Compose.polynomial_eval_mono verifier hbits
  have hser := serializer_bound (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) x w fuel
  have hser' := TM2Compose.polynomial_eval_mono (serializerPolynomial (width+3)) hsize
  have hword := Source284TaggedMarkerSeed.word_length
    (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc)
  change (word (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc)).length =
    1+3*(width+3) at hword
  dsimp only [bits] at hclean hclean' hver
  have hrun : fuel ≤ (runtimePolynomial width simulation verifier witness).eval n := by
    rw [runtimePolynomial_eval]
    change fuel ≤ simulation.eval (2*s+6)+(cleanupPolynomial width).eval (12*s+37)+
      verifier.eval (12*s+37)+4
    omega
  refine ⟨hrun,?_⟩
  rw [runwayPolynomial_eval]
  change _ ≤ (runtimePolynomial width simulation verifier witness).eval n +
      (serializerPolynomial (width+3)).eval s + (3*(width+3)+5) ∧
    _ ≤ (runtimePolynomial width simulation verifier witness).eval n +
      (serializerPolynomial (width+3)).eval s + (3*(width+3)+5)
  constructor <;> omega

end Shared.Beeping.NPcoNP.Source284VerifierUniformBudget
