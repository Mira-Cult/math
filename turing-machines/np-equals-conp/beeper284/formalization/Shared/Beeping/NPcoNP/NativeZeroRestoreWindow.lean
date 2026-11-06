import Shared.Beeping.NPcoNP.NativeZeroRestore
import Shared.Beeping.NPcoNP.NativeHalfSelectorWindow

/-! The five-zero-block bank and finite filled control run provide the exact
forward and reverse delimiter patterns for the literal zero restoration. -/
namespace Shared.Beeping.NPcoNP.NativeZeroRestoreWindow
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem holds_ones (k : Nat) (h : Int) (t : Int → Bool)
    (ones : ∀ i : Nat, i<k → t (h+(i : Int))=true) :
    Holds t h (List.replicate k true) := by
  induction k generalizing h with
  | zero => simp [Holds]
  | succ k ih =>
    simp only [List.replicate_succ,Holds]
    refine ⟨by simpa using ones 0 (by omega),?_⟩
    apply ih (h+1)
    intro i hi
    have he : h+1+(i : Int)=h+((i+1 : Nat) : Int) := by push_cast; omega
    rw [he]
    exact ones (i+1) (by omega)

/-- The reversed control/bank word has no adjacent-zero boundary inside it. -/
theorem reverse_prefix (r : Nat) :
    Prefix (unaryBankPrefix r (List.replicate 5 0)).reverse := by
  have hrep : List.replicate r true ++ [true] = true :: List.replicate r true := by
    induction r with
    | zero => rfl
    | succ r ih => simp [List.replicate_succ,ih]
  have he : (unaryBankPrefix r (List.replicate 5 0)).reverse =
      true :: ((encode (List.replicate 5 0)).reverse ++ List.replicate r true) := by
    simp [unaryBankPrefix,encode,block,List.replicate_succ,List.reverse_append,hrep]
  rw [he]
  exact Prefix.one (prefix_append (prefix_reverse_bank (List.replicate 5 0)) (prefix_ones r))

/-- A filled run, separator and five zero blocks, followed by the temporarily
cleared zero block, yield both exact scan windows. -/
theorem zero_windows (h separator : Int) (t : Int → Bool)
    (hlong : h+7≤separator)
    (hz1 : t (h+3)=false) (hz2 : t (h+4)=false)
    (ones : ∀ q, h+5≤q → q<separator → t q=true)
    (hsep : t separator=false)
    (bank : Holds t (separator+1) (encode (List.replicate 5 0) ++ [false,false])) :
    let r := (separator-(h+6)).toNat
    let ys := unaryBankPrefix r (List.replicate 5 0)
    Prefix ys ∧ Prefix ys.reverse ∧
      downHolds t (separator+9) (ys.reverse ++ [false,false]) ∧
      Holds t (h+5) (ys ++ [false,false,false]) ∧
      separator+11=(h+2)+(ys.length : Int)+4 := by
  dsimp only
  let r := (separator-(h+6)).toNat
  let ys := unaryBankPrefix r (List.replicate 5 0)
  have hr : (r : Int)=separator-(h+6) := Int.toNat_of_nonneg (by omega)
  have hk : h+5+((r+1 : Nat) : Int)=separator := by push_cast; omega
  have hlen : ys.length=r+11 := by
    simp [ys,unaryBankPrefix,List.replicate_succ]
  have hcontrol : Holds t (h+5) (List.replicate (r+1) true) := by
    apply holds_ones
    intro i hi
    apply ones <;> omega
  have hbank : Holds t separator (false :: (encode (List.replicate 5 0) ++ [false,false])) := by
    change t separator=false ∧ Holds t (separator+1) (encode (List.replicate 5 0) ++ [false,false])
    exact ⟨hsep,bank⟩
  have hall := holds_append_intro t (h+5) (List.replicate (r+1) true)
    (false :: (encode (List.replicate 5 0) ++ [false,false])) hcontrol (by simpa only [List.length_replicate,hk] using hbank)
  have he : ys ++ [false,false,false] = List.replicate (r+1) true ++
      (false :: (encode (List.replicate 5 0) ++ [false,false])) := by
    simp [ys,unaryBankPrefix,encode,block,List.replicate_succ,List.append_assoc]
  have hright : Holds t (h+5) (ys ++ [false,false,false]) := by rw [he]; exact hall
  have hy : Prefix ys := prefix_unaryBank r (List.replicate 5 0)
  have hx : Prefix ys.reverse := reverse_prefix r
  have hys : Holds t (h+5) ys := by
    exact holds_prefix_word t (h+5) ys [false,false,false] hright
  have hleft : Holds t (h+3) ([false,false] ++ ys) := by
    change t (h+3)=false ∧ t (h+3+1)=false ∧ Holds t (h+3+1+1) ys
    have ha : h+3+1=h+4 := by omega
    have hb : h+3+1+1=h+5 := by omega
    have hc : h+4+1=h+5 := by omega
    simpa only [ha,hb,hc] using And.intro hz1 (And.intro hz2 hys)
  have hreverse := holds_reverse t (h+3) ([false,false] ++ ys) hleft
  have hstart : h+3+((([false,false] ++ ys).length : Nat) : Int)-1=separator+9 := by
    simp only [List.length_append,List.length_cons,List.length_nil,hlen,Nat.cast_add,Nat.cast_ofNat]
    omega
  have hreverse' : downHolds t (separator+9) (ys.reverse ++ [false,false]) := by
    have hw : ([false,false] ++ ys).reverse=ys.reverse ++ [false,false] := by simp
    rw [hstart,hw] at hreverse
    exact hreverse
  refine ⟨hy,hx,hreverse',hright,?_⟩
  rw [hlen]
  push_cast
  omega

#print axioms reverse_prefix
#print axioms zero_windows
end Shared.Beeping.NPcoNP.NativeZeroRestoreWindow
