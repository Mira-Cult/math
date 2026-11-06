import Shared.Beeping.NPcoNP.NativeBankReturnGeneric
import Shared.Beeping.NPcoNP.NativeHalfReturn23

/-! State-23 return across an arbitrary finite unary bank prefix. The theorem
is a supplied-layout result and makes no reachability claim. -/
namespace Shared.Beeping.NPcoNP.NativeBankReturn23Generic
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfReturn23
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeZeroWindowGeneric
open Shared.Beeping.NPcoNP.NativeZeroRestoreWindow
open Shared.Beeping.NPcoNP.NativeBankReturnGeneric
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Given a finite positive control run and any encoded prefix, the literal
state-23 return reaches state 1, leaves the complete tape unchanged, and
emits no events. The exact duration counts every cell in the scan. -/
theorem return23_generic_weak (h separator : Int) (t : Int → Bool)
    (values : List Nat) (tail : List Bool) (hlong : h+5≤separator)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (marker : t (h+3)=true)
    (control : ∀ q, h+4≤q → q<separator → t q=true)
    (hsep : t separator=false) (bank : Holds t (separator+1) (encode values ++ tail)) :
    let r := (separator-(h+5)).toNat
    let ys := unaryBankPrefix r values
    silentSegment machine (cfg 23 (separator+((encode values).length : Int)-1) t)
      (cfg 1 h t) (ys.length+3) := by
  dsimp only
  let r := (separator-(h+5)).toNat
  let ys := unaryBankPrefix r values
  let finish := separator+((encode values).length : Int)
  have hr : (r : Int)=separator-(h+5) := Int.toNat_of_nonneg (by omega)
  have hk : h+4+((r+1 : Nat) : Int)=separator := by push_cast; omega
  have hlen : ys.length=r+1+(encode values).length := by
    have hh := congrArg List.length (prefix_word r values)
    simp only [List.length_append,List.length_cons,List.length_nil,encode,block_length] at hh
    change (unaryBankPrefix r values).length=r+1+(encode values).length
    omega
  have hc : Holds t (h+4) (List.replicate (r+1) true) := by
    apply holds_ones
    intro i hi
    apply control <;> omega
  have hprefix : Holds t (separator+1) (encode values) :=
    holds_prefix_word t (separator+1) _ tail bank
  have hbank : Holds t separator (false :: encode values) := by
    exact ⟨hsep,hprefix⟩
  have hall := holds_append_intro t (h+4) (List.replicate (r+1) true)
    (false :: encode values) hc (by simpa only [List.length_replicate,hk] using hbank)
  have hword : ys ++ [false] = List.replicate (r+1) true ++ (false :: encode values) := by
    have hh := prefix_word r values
    simpa [ys,encode,block,List.append_assoc] using hh
  have hyEnd : Holds t (h+4) (ys ++ [false]) := by rw [hword]; exact hall
  have hforward : Holds t (h+1) ([false,false,true] ++ ys ++ [false]) := by
    change t (h+1)=false ∧ t (h+1+1)=false ∧ t (h+1+1+1)=true ∧
      Holds t (h+1+1+1+1) (ys ++ [false])
    have he1 : h+1+1=h+2 := by omega
    have he2 : h+2+1=h+3 := by omega
    have he3 : h+3+1=h+4 := by omega
    simpa only [he1,he2,he3] using And.intro hp1 (And.intro hp2 (And.intro marker hyEnd))
  have hback := holds_reverse t (h+1) ([false,false,true] ++ ys ++ [false]) hforward
  let xs := ys.reverse ++ [true]
  have hx : Prefix xs := by
    apply prefix_drop_false
    exact return_prefix_generic r values
  have hstart : h+1+((([false,false,true] ++ ys ++ [false]).length : Nat) : Int)-1=finish := by
    simp only [List.length_append,List.length_cons,List.length_nil,hlen,Nat.cast_add,Nat.cast_ofNat]
    dsimp [finish]
    omega
  have hwback : ([false,false,true] ++ ys ++ [false]).reverse = false :: (xs ++ [false,false]) := by
    simp [xs,List.reverse_append,List.append_assoc]
  rw [hstart,hwback] at hback
  have htail : downHolds t (finish-1) (xs ++ [false,false]) := hback.2
  obtain ⟨s,hs⟩ := shape_of_prefix xs hx
  have hscan := return_scan s (finish-1) t (by simpa only [hs] using htail)
  have hslen : (bits s).length=ys.length+1 := by rw [hs]; simp [xs]
  have hfinish : finish-1-((bits s).length : Int)-2=h := by rw [hslen,hlen]; dsimp [finish]; push_cast; omega
  have htime : (bits s).length+2=ys.length+3 := by rw [hslen]
  simpa only [hfinish,htime,finish,ys,r] using hscan

/-- Earlier interface retaining its stronger separation hypothesis. -/
theorem return23_generic (h separator : Int) (t : Int → Bool)
    (values : List Nat) (tail : List Bool) (hlong : h+6≤separator)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (marker : t (h+3)=true)
    (control : ∀ q, h+4≤q → q<separator → t q=true)
    (hsep : t separator=false) (bank : Holds t (separator+1) (encode values ++ tail)) :
    let r := (separator-(h+5)).toNat
    let ys := unaryBankPrefix r values
    silentSegment machine (cfg 23 (separator+((encode values).length : Int)-1) t)
      (cfg 1 h t) (ys.length+3) :=
  return23_generic_weak h separator t values tail (by omega) hp1 hp2 marker control hsep bank

#print axioms return23_generic_weak
#print axioms return23_generic
end Shared.Beeping.NPcoNP.NativeBankReturn23Generic
