import Shared.Beeping.NPcoNP.Grammar284InfiniteIncrement
import Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch

/-! A parser window whose encoded bank is followed by a separate zero block
and an infinite blank tail. This reserve supports native positive HALF. -/
namespace Shared.Beeping.NPcoNP.Grammar284ReservedWindow
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284InfiniteIncrement
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

def ReservedWindow (state : Fin 185) (bank : Bank 12) (origin separator : Int)
    (t : Int → Bool) : Prop :=
  ∃ (path : Path) (name : String) (more : List Nat),
    graphLeaf state=some (path,name) ∧ origin+59≤separator ∧ Holds t origin path ∧
    (∀ q, q<origin → t q=false) ∧
    (∀ q, origin+((path.length : Nat) : Int)-1<q → q<separator-1 → t q=false) ∧
    t (separator-1)=true ∧ t separator=false ∧
    Holds t (separator+1) (encode (arrayBank bank++more) ++ [true,false]) ∧
    (∀ q, separator+2+((encode (arrayBank bank++more)).length : Int)≤q → t q=false)

theorem infinite_of_reserved (state : Fin 185) (bank : Bank 12) (origin separator : Int)
    (t : Int → Bool) (window : ReservedWindow state bank origin separator t) :
    InfiniteWindow state bank origin separator t := by
  obtain ⟨path,name,more,hleaf,room,word,left,gap,right,sep,hbank,htail⟩ := window
  refine ⟨path,name,more++[0],hleaf,room,word,left,gap,right,sep,?_,?_⟩
  · simpa [encode_append,encode,block,List.append_assoc] using hbank
  · intro q hq
    apply htail
    have he : (encode (arrayBank bank++(more++[0]))).length=(encode (arrayBank bank++more)).length+2 := by
      simp [encode_append,encode,block,List.append_assoc,Nat.add_assoc]
    rw [he] at hq
    push_cast at hq
    omega

/-- The last cell of the explicit reserve extends an already-blank tail by one. -/
theorem tail_from_end (t : Int → Bool) (start : Int) (word : List Bool)
    (bank : Holds t start (word ++ [true,false]))
    (tail : ∀ q, start+((word.length : Nat) : Int)+2≤q → t q=false) :
    ∀ q, start+((word.length : Nat) : Int)+1≤q → t q=false := by
  obtain ⟨_,hreserve⟩ := holds_split t start word [true,false] bank
  have hz : t (start+((word.length : Nat) : Int)+1)=false := by simpa [Holds] using hreserve.2.1
  intro q hq
  by_cases he : q=start+((word.length : Nat) : Int)+1
  · simpa [he] using hz
  · exact tail q (by omega)

#print axioms infinite_of_reserved
end Shared.Beeping.NPcoNP.Grammar284ReservedWindow
