import Shared.Beeping.NPcoNP.NativeZeroRestoreWindow

/-! Restoration windows for an arbitrary finite prefix of unary bank values. -/
namespace Shared.Beeping.NPcoNP.NativeZeroWindowGeneric
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeZeroRestoreWindow
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem boundary_word (values : List Nat) :
    values.flatMap (fun z => false :: List.replicate (z+1) true) ++ [false] =
      false :: encode values := by
  induction values with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,encode,List.cons_append,List.append_assoc,ih]
    simp [block,List.append_assoc]

theorem prefix_word (r : Nat) (values : List Nat) :
    unaryBankPrefix r values ++ [false] = encode (r::values) := by
  simp only [unaryBankPrefix,encode,block,List.append_assoc]
  rw [boundary_word]
  simp [List.append_assoc]

theorem prefix_drop_false {xs : List Bool} (h : Prefix (false::xs)) : Prefix xs := by
  cases h with
  | zeroOne h => exact Prefix.one h

theorem reverse_prefix_generic (r : Nat) (values : List Nat) :
    Prefix (unaryBankPrefix r values).reverse := by
  have hh := prefix_reverse_bank (r::values)
  rw [←prefix_word r values] at hh
  apply prefix_drop_false
  simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append] using hh

theorem zero_windows_generic_min_gap (h separator : Int) (t : Int → Bool) (values : List Nat)
    (hlong : h+6≤separator)
    (hz1 : t (h+3)=false) (hz2 : t (h+4)=false)
    (ones : ∀ q, h+5≤q → q<separator → t q=true)
    (hsep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ [false,false])) :
    let r := (separator-(h+6)).toNat
    let ys := unaryBankPrefix r values
    let pos := separator+1+((encode values).length : Int)
    Prefix ys ∧ Prefix ys.reverse ∧
      downHolds t (pos-2) (ys.reverse ++ [false,false]) ∧
      Holds t (h+5) (ys ++ [false,false,false]) ∧
      pos=(h+2)+(ys.length : Int)+4 := by
  dsimp only
  let r := (separator-(h+6)).toNat
  let ys := unaryBankPrefix r values
  let pos := separator+1+((encode values).length : Int)
  have hr : (r : Int)=separator-(h+6) := Int.toNat_of_nonneg (by omega)
  have hk : h+5+((r+1 : Nat) : Int)=separator := by push_cast; omega
  have hlen : ys.length=r+1+(encode values).length := by
    have hh := congrArg List.length (prefix_word r values)
    simp only [List.length_append,List.length_cons,List.length_nil,encode,block_length] at hh
    change (unaryBankPrefix r values).length=r+1+(encode values).length
    omega
  have hcontrol : Holds t (h+5) (List.replicate (r+1) true) := by
    apply holds_ones
    intro i hi
    apply ones <;> omega
  have hbank : Holds t separator (false :: (encode values ++ [false,false])) := by
    change t separator=false ∧ Holds t (separator+1) (encode values ++ [false,false])
    exact ⟨hsep,bank⟩
  have hall := holds_append_intro t (h+5) (List.replicate (r+1) true)
    (false :: (encode values ++ [false,false])) hcontrol (by simpa only [List.length_replicate,hk] using hbank)
  have he : ys ++ [false,false,false] = List.replicate (r+1) true ++
      (false :: (encode values ++ [false,false])) := by
    have hh : ys ++ [false] = List.replicate (r+1) true ++ (false :: encode values) := by
      have hp := prefix_word r values
      simpa [ys,encode,block,List.append_assoc] using hp
    calc
      ys ++ [false,false,false] = (ys ++ [false]) ++ [false,false] := by simp [List.append_assoc]
      _ = (List.replicate (r+1) true ++ (false :: encode values)) ++ [false,false] := by rw [hh]
      _ = _ := by simp [List.append_assoc]
  have hright : Holds t (h+5) (ys ++ [false,false,false]) := by rw [he]; exact hall
  have hy : Prefix ys := prefix_unaryBank r values
  have hx : Prefix ys.reverse := reverse_prefix_generic r values
  have hys : Holds t (h+5) ys := holds_prefix_word t (h+5) ys [false,false,false] hright
  have hleft : Holds t (h+3) ([false,false] ++ ys) := by
    change t (h+3)=false ∧ t (h+3+1)=false ∧ Holds t (h+3+1+1) ys
    have ha : h+3+1=h+4 := by omega
    have hb : h+3+1+1=h+5 := by omega
    have hc : h+4+1=h+5 := by omega
    simpa only [ha,hb,hc] using And.intro hz1 (And.intro hz2 hys)
  have hreverse := holds_reverse t (h+3) ([false,false] ++ ys) hleft
  have hstart : h+3+((([false,false] ++ ys).length : Nat) : Int)-1=pos-2 := by
    simp only [List.length_append,List.length_cons,List.length_nil,hlen,Nat.cast_add,Nat.cast_ofNat]
    dsimp [pos]
    omega
  have hreverse' : downHolds t (pos-2) (ys.reverse ++ [false,false]) := by
    have hw : ([false,false] ++ ys).reverse=ys.reverse ++ [false,false] := by simp
    rw [hstart,hw] at hreverse
    exact hreverse
  refine ⟨hy,hx,hreverse',hright,?_⟩
  rw [hlen]
  dsimp [pos]
  push_cast
  omega

theorem zero_windows_generic (h separator : Int) (t : Int → Bool) (values : List Nat)
    (hlong : h+7≤separator)
    (hz1 : t (h+3)=false) (hz2 : t (h+4)=false)
    (ones : ∀ q, h+5≤q → q<separator → t q=true)
    (hsep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ [false,false])) :
    let r := (separator-(h+6)).toNat
    let ys := unaryBankPrefix r values
    let pos := separator+1+((encode values).length : Int)
    Prefix ys ∧ Prefix ys.reverse ∧
      downHolds t (pos-2) (ys.reverse ++ [false,false]) ∧
      Holds t (h+5) (ys ++ [false,false,false]) ∧
      pos=(h+2)+(ys.length : Int)+4 := by
  exact zero_windows_generic_min_gap h separator t values (by omega) hz1 hz2 ones hsep bank

#print axioms boundary_word
#print axioms reverse_prefix_generic
#print axioms zero_windows_generic_min_gap
#print axioms zero_windows_generic
end Shared.Beeping.NPcoNP.NativeZeroWindowGeneric
