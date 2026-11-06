import Shared.Beeping.NPcoNP.NativeFirstReturn25
import Shared.Beeping.NPcoNP.NativeZeroWindowGeneric

/-! A literal state-25 return across an arbitrary finite unary bank prefix. -/
namespace Shared.Beeping.NPcoNP.NativeBankReturnGeneric
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfOddReturn
open Shared.Beeping.NPcoNP.NativeHalfOddFinish
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeZeroRestoreWindow
open Shared.Beeping.NPcoNP.NativeZeroWindowGeneric
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem prefix_false_extend {xs : List Bool} (h : Prefix (false::xs)) :
    Prefix (false::(xs ++ [true])) := by
  cases h with
  | zeroOne h => exact Prefix.zeroOne (prefix_append h (Prefix.one Prefix.nil))

theorem return_prefix_generic (r : Nat) (values : List Nat) :
    Prefix (false :: ((unaryBankPrefix r values).reverse ++ [true])) := by
  apply prefix_false_extend
  have hh := prefix_reverse_bank (r::values)
  rw [←prefix_word r values] at hh
  simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append] using hh

/-- Given a finite control run and arbitrary encoded preceding bank values,
state 25 returns silently to state 1 with the tape unchanged. -/
theorem return25_generic_min_gap (h separator : Int) (t : Int → Bool)
    (values : List Nat) (tail : List Bool) (hlong : h+6≤separator)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false) (hp3 : t (h+3)=false)
    (control : ∀ q, h+4≤q → q<separator → t q=true)
    (hsep : t separator=false) (bank : Holds t (separator+1) (encode values ++ tail)) :
    let r := (separator-(h+6)).toNat
    let ys := unaryBankPrefix r values
    silentSegment machine (cfg 25 (separator+((encode values).length : Int)) t)
      (cfg 1 h t) (ys.length+5) := by
  dsimp only
  let r := (separator-(h+6)).toNat
  let ys := unaryBankPrefix r values
  let finish := separator+((encode values).length : Int)
  have hr : (r : Int)=separator-(h+6) := Int.toNat_of_nonneg (by omega)
  have hk : h+5+((r+1 : Nat) : Int)=separator := by push_cast; omega
  have hlen : ys.length=r+1+(encode values).length := by
    have hh := congrArg List.length (prefix_word r values)
    simp only [List.length_append,List.length_cons,List.length_nil,encode,block_length] at hh
    change (unaryBankPrefix r values).length=r+1+(encode values).length
    omega
  have hc : Holds t (h+5) (List.replicate (r+1) true) := by
    apply holds_ones
    intro i hi
    apply control <;> omega
  have hprefix : Holds t (separator+1) (encode values) :=
    holds_prefix_word t (separator+1) _ tail bank
  have hbank : Holds t separator (false :: encode values) := by
    exact ⟨hsep,hprefix⟩
  have hall := holds_append_intro t (h+5) (List.replicate (r+1) true)
    (false :: encode values) hc (by simpa only [List.length_replicate,hk] using hbank)
  have hword : ys ++ [false] = List.replicate (r+1) true ++ (false :: encode values) := by
    have hh := prefix_word r values
    simpa [ys,encode,block,List.append_assoc] using hh
  have hyEnd : Holds t (h+5) (ys ++ [false]) := by rw [hword]; exact hall
  have hp4 : t (h+4)=true := control (h+4) (by omega) (by omega)
  have hforward : Holds t (h+2) ([false,false,true] ++ ys ++ [false]) := by
    change t (h+2)=false ∧ t (h+2+1)=false ∧ t (h+2+1+1)=true ∧
      Holds t (h+2+1+1+1) (ys ++ [false])
    have he1 : h+2+1=h+3 := by omega
    have he2 : h+3+1=h+4 := by omega
    have he3 : h+4+1=h+5 := by omega
    simpa only [he1,he2,he3] using And.intro hp2 (And.intro hp3 (And.intro hp4 hyEnd))
  have hback := holds_reverse t (h+2) ([false,false,true] ++ ys ++ [false]) hforward
  let xs := false :: (ys.reverse ++ [true])
  have hx : Prefix xs := return_prefix_generic r values
  have hstart : h+2+((([false,false,true] ++ ys ++ [false]).length : Nat) : Int)-1=finish := by
    simp only [List.length_append,List.length_cons,List.length_nil,hlen,Nat.cast_add,Nat.cast_ofNat]
    dsimp [finish]
    omega
  have hwback : ([false,false,true] ++ ys ++ [false]).reverse=xs ++ [false,false] := by
    simp [xs,List.reverse_append,List.append_assoc]
  rw [hstart,hwback] at hback
  obtain ⟨s,hs⟩ := shape_of_prefix xs hx
  have hscan := return_scan25 s finish t (by simpa only [hs] using hback)
  have hslen : (bits s).length=ys.length+2 := by rw [hs]; simp [xs]
  have hfinish : finish-((bits s).length : Int)-2=h+1 := by rw [hslen,hlen]; dsimp [finish]; push_cast; omega
  have hscan' : silentSegment machine (cfg 25 finish t) (cfg 95 (h+1) t)
      ((bits s).length+2) := by simpa only [hfinish] using hscan
  have h95 := oneSeg machine _ _ (step95_zero (h+1) t hp1)
  have h95' : silentSegment machine (cfg 95 (h+1) t) (cfg 1 h t) 1 := by
    have he : h+1-1=h := by omega
    simpa only [he] using h95
  have all := segAdd machine _ _ _ ((bits s).length+2) 1 hscan' h95'
  have htime : (bits s).length+2+1=ys.length+5 := by rw [hslen]
  simpa only [htime,finish,ys,r] using all

theorem return25_generic (h separator : Int) (t : Int → Bool)
    (values : List Nat) (tail : List Bool) (hlong : h+7≤separator)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false) (hp3 : t (h+3)=false)
    (control : ∀ q, h+4≤q → q<separator → t q=true)
    (hsep : t separator=false) (bank : Holds t (separator+1) (encode values ++ tail)) :
    let r := (separator-(h+6)).toNat
    let ys := unaryBankPrefix r values
    silentSegment machine (cfg 25 (separator+((encode values).length : Int)) t)
      (cfg 1 h t) (ys.length+5) := by
  exact return25_generic_min_gap h separator t values tail (by omega) hp1 hp2 hp3 control hsep bank

#print axioms return_prefix_generic
#print axioms return25_generic_min_gap
#print axioms return25_generic
end Shared.Beeping.NPcoNP.NativeBankReturnGeneric
