import Shared.Beeping.NPcoNP.Source284CertificateProbeRun

/-! The exact sentinel shape produced by the two-sided loader, and the
meaning of its first tagged witness marker. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284CertificateProbeLayout

open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284CertificateProbeRun (body mode cost)
open Shared.Beeping.NPcoNP.Source284TwoSidedScaledQuadraticWindow (leftData)

def firstZeros (k n : Nat) : Nat := k*(n*n)+6*n+6
def secondZeros (n : Nat) : Nat := 2*n+1

theorem pairTape_zeros (n certificate : Nat) :
    pairTape (List.replicate n false) certificate = 2^(2*n+1)*(2*certificate+1) := by
  rw [Source284UnaryPairScanner.zero_pairTape,Source284ScratchSentinel.unaryPairs_stack,pow_succ]
  ring

/-- The loader's precise left half has two self-delimiting markers beyond
its paid zero block. -/
theorem leftData_eq_body (k : Nat) (w : List Bool) (frame : Nat) :
    leftData k w (4*frame) = body (firstZeros k w.length) (secondZeros w.length) frame := by
  let n := w.length
  let p := k*(n*n)+1
  let z := 2*n+1
  have h4 : 4^(n+1)=2^(2*(n+1)) := by rw [Nat.pow_mul]
  have hpow : 4^(n+1)*4^(n+1)*2^p*2^z = 2^(firstZeros k n) := by
    rw [h4,← pow_add,← pow_add,← pow_add]
    congr 1
    dsimp [p,z,firstZeros]
    omega
  have hd : leftData k w (4*frame) =
      (4^(n+1)*4^(n+1)*2^p*2^z)*(2*(2^z*(2*(4*frame)+1))+1) := by
    dsimp [leftData,n,p,z]
    rw [pairTape_zeros,pairTape_zeros]
    ring
  rw [hd,hpow]
  rfl

theorem cost_formula (k n : Nat) : cost (firstZeros k n) (secondZeros n) =
    2*k*(n*n)+16*n+26 := by
  simp [cost,firstZeros,secondZeros]
  ring

/-- For this tagged frame, the first marker is one exactly when the witness
is nonempty; the arbitrary high suffix does not affect this bit. -/
theorem mode_frame (w : List Bool) (suffix : Nat) :
    mode (Source284Parser.encodeFrame w suffix) = if w=[] then 0 else 1 := by
  cases w with
  | nil => simp [mode,Source284Parser.encodeFrame,Nat.testBit_zero]
  | cons b bs =>
    have hodd : Source284Parser.encodeFrame (b::bs) suffix % 2=1 := by
      cases b <;> simp [Source284Parser.encodeFrame] <;> omega
    have hb : (Source284Parser.encodeFrame (b::bs) suffix).testBit 0 = true := by
      simp [Nat.testBit_zero,Source284WitnessScanner.bit_decide_mod,hodd]
    simp [mode,hb]

end Shared.Beeping.NPcoNP.Source284CertificateProbeLayout
