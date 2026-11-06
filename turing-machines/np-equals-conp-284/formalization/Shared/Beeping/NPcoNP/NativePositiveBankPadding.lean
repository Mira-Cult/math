import Shared.Beeping.NPcoNP.NativePositiveSelectorDirect

/-! Carry an arbitrary supplied right padding through a positive bank operation. -/
namespace Shared.Beeping.NPcoNP.NativePositiveBankPadding
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeManyBankResult
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

/-- Matching input and output bank prefixes end at the same cell. The
post-operation right frame carries every supplied padding cell. -/
theorem positive_bank_padding (t out : Int → Bool) (x : Int) (w : Nat) (vs : List Nat) (pad : List Bool)
    (bank : Holds t x ((encode ((w+1)::vs) ++ [false,false]) ++ pad))
    (result : Holds out x (encode (w::vs) ++ [true,false,false]))
    (frame : ∀ q, x+2+((List.replicate w true ++ vs.flatMap
      (fun z => false :: List.replicate (z+1) true)).length : Int)<q → out q=t q) :
    Holds out x ((encode (w::vs) ++ [true,false,false]) ++ pad) := by
  let suffix := List.replicate w true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
  have hlen : (encode (w::vs)).length=suffix.length+2 := by
    have h := prefix_length w vs
    simp only [unaryBankPrefix,List.length_append,List.length_replicate,List.length_flatMap] at h
    dsimp [suffix]
    simp only [List.length_append,List.length_replicate,List.length_flatMap]
    omega
  have hlen' : (encode ((w+1)::vs)).length=suffix.length+3 := by
    have h := prefix_length (w+1) vs
    simp only [unaryBankPrefix,List.length_append,List.length_replicate,List.length_flatMap] at h
    dsimp [suffix]
    simp only [List.length_append,List.length_replicate,List.length_flatMap]
    omega
  have hp : (encode ((w+1)::vs) ++ [false,false]).length =
      (encode (w::vs) ++ [true,false,false]).length := by
    simp only [List.length_append,List.length_cons,List.length_nil,hlen,hlen']
  have ht := holds_append_tail t x (encode ((w+1)::vs) ++ [false,false]) pad bank
  rw [hp] at ht
  have hpos : x+(((encode (w::vs) ++ [true,false,false]).length : Nat):Int)=
      x+(suffix.length : Int)+5 := by
    simp only [List.length_append,List.length_cons,List.length_nil,hlen]
    push_cast
    omega
  have ht' : Holds out (x+(((encode (w::vs) ++ [true,false,false]).length : Nat):Int)) pad := by
    rw [hpos] at ht ⊢
    apply holds_transport t out _ _ ht
    intro q hq _
    symm
    apply frame
    change x+2+(suffix.length : Int)<q
    omega
  exact holds_append_intro out x (encode (w::vs) ++ [true,false,false]) pad result ht'

#print axioms positive_bank_padding
end Shared.Beeping.NPcoNP.NativePositiveBankPadding
