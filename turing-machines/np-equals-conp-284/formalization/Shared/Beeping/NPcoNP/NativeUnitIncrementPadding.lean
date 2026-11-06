import Shared.Beeping.NPcoNP.NativeUnitSelectorBankIncrement

/-! Right-padding preservation for a supplied unit bank increment. -/
namespace Shared.Beeping.NPcoNP.NativeUnitIncrementPadding
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

/-- The increment consumes the supplied blank after the original encoding;
all further supplied padding is preserved by the right tape frame. -/
theorem unit_increment_padding (t out : Int → Bool) (x : Int) (v : Nat) (rest : List Nat) (pad : List Bool)
    (bank : Holds t x ((encode (v::rest) ++ [false]) ++ pad))
    (result : Holds out x (encode ((v+1)::rest)))
    (frame : ∀ q, x+(((v+1)+(encode rest).length : Nat):Int)<q → out q=t q) :
    Holds out x (encode ((v+1)::rest) ++ pad) := by
  have hlen : (encode (v::rest) ++ [false]).length=(encode ((v+1)::rest)).length := by
    simp only [List.length_append,List.length_cons,List.length_nil,encode,block_length]
    omega
  have ht := holds_append_tail t x (encode (v::rest) ++ [false]) pad bank
  rw [hlen] at ht
  have ht' : Holds out (x+(((encode ((v+1)::rest)).length : Nat):Int)) pad := by
    apply holds_transport t out _ _ ht
    intro q hq _
    symm
    apply frame
    have he : (encode ((v+1)::rest)).length=(v+1)+(encode rest).length+2 := by
      simp only [encode,List.length_append,block_length]
      omega
    rw [he] at hq
    push_cast at hq
    omega
  exact holds_append_intro out x (encode ((v+1)::rest)) pad result ht'

#print axioms unit_increment_padding
end Shared.Beeping.NPcoNP.NativeUnitIncrementPadding
