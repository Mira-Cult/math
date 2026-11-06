import Shared.Beeping.NPcoNP.NativePositiveBankDecode
import Shared.Beeping.NPcoNP.Parent290Coalesced

/-! Bank-value agreement for the physical positive result and the coalesced
graph's row 8. The machine's subsequent control alignment is not proved here. -/
namespace Shared.Beeping.NPcoNP.NativePositiveGraphBank
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeFifthPositive
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem ofFn_write10 (bank : Bank 12) (v : Nat) :
    List.ofFn (write bank 10 v) = (List.ofFn bank).set 10 v := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_set, write]
    by_cases h : i=10
    · subst i; simp
    · have hn : (⟨i, by simpa using h1⟩ : Fin 12) ≠ 10 := by
        intro he; have hh := congrArg Fin.val he; simp at hh; exact h hh
      simp [h,Ne.symm h,hn]

theorem row8_positive (bank : Bank 12) (v : Nat) (hv : bank 10=v+1) :
    target.system.step ⟨8,bank⟩=(⟨9,write bank 10 v⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,hv]

theorem write_list (bank : Bank 12) (values : List Nat) (v z : Nat)
    (hlen : values.length=10) (h : List.ofFn bank = values ++ [v+1,z]) :
    List.ofFn (write bank 10 v) = values ++ [v,z] := by
  rw [ofFn_write10,h,List.set_append_right 10 v (by omega),hlen]
  simp

theorem bank10_of_list (bank : Bank 12) (values : List Nat) (v z : Nat)
    (hlen : values.length=10) (h : List.ofFn bank = values ++ [v+1,z]) :
    bank 10=v+1 := by
  have he := congrArg (fun l : List Nat => l[10]?) h
  simpa [List.getElem?_ofFn, List.getElem?_append, hlen] using he

/-- Readback matches the graph step's updated twelve-register bank. The
remaining physical bank and reserve are returned as the decoder's tail. -/
theorem decoded_matches_row8 (t : Int → Bool) (start : Int) (values : List Nat)
    (v z : Nat) (rest : List Nat) (bank : Bank 12) (hlen : values.length=10)
    (hbank : List.ofFn bank=values ++ [v+1,z])
    (hp : Holds t start (encode values))
    (hu : Holds t (start+((encode values).length : Int))
      (encode (v::z::rest) ++ [true,false,false])) :
    let result := (target.system.step ⟨8,bank⟩).1
    let tail := encode rest ++ [true,false,false]
    decode 12 (readCells t start (encode (List.ofFn result.bank) ++ tail).length)=
      some (List.ofFn result.bank,tail) ∧
    result.state=9 ∧ (target.system.step ⟨8,bank⟩).2=[] := by
  dsimp only
  have hr := row8_positive bank v (bank10_of_list bank values v z hlen hbank)
  have hb := write_list bank values v z hlen hbank
  have hw := holds_append_intro t start (encode values)
    (encode (v::z::rest) ++ [true,false,false]) hp hu
  have he : encode (values ++ [v,z]) ++ (encode rest ++ [true,false,false]) =
      encode values ++ (encode (v::z::rest) ++ [true,false,false]) := by
    simp [encode_append,encode,List.append_assoc]
  have hh : Holds t start (encode (values ++ [v,z]) ++ (encode rest ++ [true,false,false])) := by
    rw [he]
    exact hw
  rw [hr]
  simp only [Prod.fst,Prod.snd]
  rw [hb,read_of_holds t start _ hh]
  have hl : (values ++ [v,z]).length=12 := by simp [hlen]
  have hd := decode_encode (values ++ [v,z]) (encode rest ++ [true,false,false])
  rw [hl] at hd
  exact ⟨hd,trivial,trivial⟩

#print axioms row8_positive
#print axioms decoded_matches_row8
end Shared.Beeping.NPcoNP.NativePositiveGraphBank
