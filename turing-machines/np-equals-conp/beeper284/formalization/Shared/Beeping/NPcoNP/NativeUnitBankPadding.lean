import Shared.Beeping.NPcoNP.NativeIncBank

/-! A finite increment consumes one blank of right padding. -/
namespace Shared.Beeping.NPcoNP.NativeUnitBankPadding
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

/-- Given the exact increment frame, an input with `extra+1` trailing zeros
has `extra` trailing zeros after the bank grows by one cell. -/
theorem increment_preserves_padding (t out : Int → Bool) (base : Int)
    (v extra : Nat) (rest : List Nat)
    (input : Holds t base (encode (v::rest) ++ List.replicate (extra+1) false))
    (updated : Holds out base (encode ((v+1)::rest)))
    (frame : ∀ q, base+(((v+1)+(encode rest).length : Nat):Int)<q → out q=t q) :
    Holds out base (encode ((v+1)::rest) ++ List.replicate extra false) := by
  let old := encode (v::rest)
  let values := encode ((v+1)::rest)
  have hlen : values.length=old.length+1 := by
    simp [values,old,encode,block_length]
    omega
  have htail := holds_append_tail t base old (List.replicate (extra+1) false) input
  have htail' : Holds t (base+(old.length : Int)+1) (List.replicate extra false) := by
    have he : List.replicate (extra+1) false = false::List.replicate extra false := by
      simp [List.replicate_succ]
    rw [he] at htail
    exact htail.2
  have hp : base+((values.length : Nat):Int)=base+(old.length : Int)+1 := by rw [hlen]; push_cast; omega
  have htail'' : Holds t (base+((values.length : Nat):Int)) (List.replicate extra false) := by
    rw [hp]
    exact htail'
  have hbound : base+(((v+1)+(encode rest).length : Nat):Int)<base+((values.length : Nat):Int) := by
    simp [values,encode,block_length]
  have hout : Holds out (base+((values.length : Nat):Int)) (List.replicate extra false) := by
    apply holds_transport t out _ _ htail''
    intro q hq _
    symm
    exact frame q (by omega)
  exact holds_append_intro out base values (List.replicate extra false) updated hout

#print axioms increment_preserves_padding
end Shared.Beeping.NPcoNP.NativeUnitBankPadding
