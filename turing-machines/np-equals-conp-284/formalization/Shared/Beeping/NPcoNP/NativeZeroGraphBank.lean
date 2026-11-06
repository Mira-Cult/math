import Shared.Beeping.NPcoNP.NativeFifthZeroNext
import Shared.Beeping.NPcoNP.Bootstrap284BankDecode
import Shared.Beeping.NPcoNP.Parent290Coalesced

/-! The literal zero-branch bank readback and the actual coalesced graph row 8.
The tape word is supplied; this module does not establish its reachability. -/
namespace Shared.Beeping.NPcoNP.NativeZeroGraphBank
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem row8_zero (bank : Bank 12) (hv : bank 10=0) :
    target.system.step ⟨8,bank⟩=(⟨10,bank⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,hv]

theorem bank10_zero_of_list (bank : Bank 12) (values : List Nat) (z : Nat)
    (hlen : values.length=10) (h : List.ofFn bank = values ++ [0,z]) : bank 10=0 := by
  have he := congrArg (fun l : List Nat => l[10]?) h
  simpa [List.getElem?_ofFn, List.getElem?_append, hlen] using he

/-- The unchanged encoded bank decodes to the graph's zero-branch bank; the
remaining encoded values and any trailing bits are returned as a tail. -/
theorem decoded_matches_row8_zero (t : Int → Bool) (start : Int) (values : List Nat)
    (z : Nat) (rest : List Nat) (extra : List Bool) (bank : Bank 12) (hlen : values.length=10)
    (hbank : List.ofFn bank=values ++ [0,z])
    (word : Holds t start (encode values ++ (encode (0::z::rest) ++ extra))) :
    let result := (target.system.step ⟨8,bank⟩).1
    let tail := encode rest ++ extra
    decode 12 (readCells t start (encode (List.ofFn result.bank) ++ tail).length)=
      some (List.ofFn result.bank,tail) ∧
    result.state=10 ∧ (target.system.step ⟨8,bank⟩).2=[] := by
  dsimp only
  have hr := row8_zero bank (bank10_zero_of_list bank values z hlen hbank)
  have he : encode (values ++ [0,z]) ++ (encode rest ++ extra) =
      encode values ++ (encode (0::z::rest) ++ extra) := by
    simp [encode_append,encode,List.append_assoc]
  have hh : Holds t start (encode (values ++ [0,z]) ++ (encode rest ++ extra)) := by
    rw [he]
    exact word
  rw [hr]
  simp only [Prod.fst,Prod.snd]
  rw [hbank,read_of_holds t start _ hh]
  have hl : (values ++ [0,z]).length=12 := by simp [hlen]
  have hd := decode_encode (values ++ [0,z]) (encode rest ++ extra)
  rw [hl] at hd
  exact ⟨hd,trivial,trivial⟩

#print axioms row8_zero
#print axioms decoded_matches_row8_zero
end Shared.Beeping.NPcoNP.NativeZeroGraphBank
