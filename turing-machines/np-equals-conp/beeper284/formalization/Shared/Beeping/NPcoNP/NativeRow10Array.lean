import Shared.Beeping.NPcoNP.NativeArrayGraphBank
import Shared.Beeping.NPcoNP.Source284GraphParserInit

/-! The actual graph row 10 in producer-array order. -/
namespace Shared.Beeping.NPcoNP.NativeRow10Array
open Shared.Beeping PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Coalescing284Map
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Parent290Coalesced
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Producer array position 6 is suffix-indexed register 5. -/
theorem array_six (bank : Bank 12) (values : List Nat) (v : Nat) (rest : List Nat)
    (hlen : values.length=6) (h : arrayBank bank=values ++ (v::rest)) : bank 5=v := by
  have he := congrArg (fun xs : List Nat => xs[6]?) h
  simpa [arrayBank,arrayToSuffix,List.getElem?_ofFn,List.getElem?_append,hlen] using he

/-- Row 10 tests the seventh producer-array value and is silent on either
branch. The positive branch changes exactly that array position. -/
theorem row10_array (bank : Bank 12) (values : List Nat) (v : Nat) (rest : List Nat)
    (hlen : values.length=6) (h : arrayBank bank=values ++ (v::rest)) :
    let result := target.system.step ⟨10,bank⟩
    result.2=[] ∧
      (if v=0 then result.1.state=11 ∧ arrayBank result.1.bank=values ++ (v::rest)
       else result.1.state=10 ∧ arrayBank result.1.bank=values ++ ((v-1)::rest)) := by
  dsimp only
  have hv := array_six bank values v rest hlen h
  have hr := Source284GraphParserInit.row10 bank
  change target.system.step ⟨10,bank⟩ =
    (if bank 5=0 then (⟨11,bank⟩,[]) else (⟨10,write bank 5 (bank 5-1)⟩,[])) at hr
  rw [hr,hv]
  by_cases hz : v=0
  · simp [hz,h]
  · simp only [hz,if_false,Prod.fst,Prod.snd]
    constructor
    · trivial
    · constructor
      · trivial
      · rw [arrayBank_write,h]
        have hi : (suffixToArray (5 : Fin 12)).val=6 := by decide
        rw [hi,List.set_append_right 6 (v-1) (by omega),hlen]
        simp

#print axioms array_six
#print axioms row10_array
end Shared.Beeping.NPcoNP.NativeRow10Array
