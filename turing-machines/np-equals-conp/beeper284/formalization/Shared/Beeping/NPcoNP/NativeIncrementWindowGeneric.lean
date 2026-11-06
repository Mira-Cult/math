import Shared.Beeping.NPcoNP.NativeZeroWindowGeneric
import Shared.Beeping.NPcoNP.NativeHalfGrammarBranch

/-! Construct both finite scan windows for row 9 from a supplied control
run and finite preceding bank blocks, without assuming the next bank value is zero. -/
namespace Shared.Beeping.NPcoNP.NativeIncrementWindowGeneric
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfGrammarBranch
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeZeroRestoreWindow
open Shared.Beeping.NPcoNP.NativeZeroWindowGeneric
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- The prepared control and preceding unary blocks determine both ordered scan
words after clearing the first cell of the next block. -/
theorem windows (h separator : Int) (t : Int → Bool) (values : List Nat) (b : Nat) (tail : List Bool)
    (hlong : h+12≤separator) (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (control : ∀ q, h+11≤q → q<separator → t q=true) (hsep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ (block b ++ tail))) :
    let r := (separator-(h+12)).toNat
    let ys := unaryBankPrefix r values
    let pos := separator+1+((encode values).length:Int)
    let u := clearAt pos t
    Prefix ys ∧ Prefix ys.reverse ∧
      downHolds u (pos-2) (ys.reverse ++ [false,false]) ∧
      Holds u (h+11) (ys ++ [false,false]) ∧
      pos=(h+8)+(ys.length : Int)+4 := by
  dsimp only
  let r := (separator-(h+12)).toNat
  let ys := unaryBankPrefix r values
  let pos := separator+1+((encode values).length:Int)
  let u := clearAt pos t
  have hr : (r : Int)=separator-(h+12) := Int.toNat_of_nonneg (by omega)
  have hk : h+11+((r+1 : Nat) : Int)=separator := by push_cast; omega
  have hlen : ys.length=r+1+(encode values).length := by
    have hh := congrArg List.length (prefix_word r values)
    change (unaryBankPrefix r values).length=r+1+(encode values).length
    simp [encode,block_length,List.length_append] at hh
    omega
  have hcontrol : Holds t (h+11) (List.replicate (r+1) true) := by
    apply holds_ones
    intro i hi
    apply control <;> omega
  have hfirst : Holds t (separator+1) (encode values) := by
    exact holds_prefix_word t _ (encode values) (block b ++ tail) bank
  have hbank : Holds t separator (false :: encode values) := ⟨hsep,hfirst⟩
  have hall := holds_append_intro t (h+11) (List.replicate (r+1) true)
    (false :: encode values) hcontrol (by simpa only [List.length_replicate,hk] using hbank)
  have hword : ys ++ [false] = List.replicate (r+1) true ++ (false :: encode values) := by
    have hh := prefix_word r values
    simpa [ys,encode,block,List.append_assoc] using hh
  have hyEnd : Holds t (h+11) (ys ++ [false]) := by rw [hword]; exact hall
  have hys : Holds t (h+11) ys := holds_prefix_word t (h+11) ys [false] hyEnd
  have hleft : Holds t (h+9) ([false,false] ++ ys) := by
    change t (h+9)=false ∧ t (h+9+1)=false ∧ Holds t (h+9+1+1) ys
    have he1 : h+9+1=h+10 := by omega
    have he2 : h+9+1+1=h+11 := by omega
    have he3 : h+10+1=h+11 := by omega
    simpa only [he1,he2,he3] using And.intro h9 (And.intro h10 hys)
  have hreverse := holds_reverse t (h+9) ([false,false] ++ ys) hleft
  have hstart : h+9+((([false,false] ++ ys).length : Nat):Int)-1=pos-2 := by
    simp only [List.length_append,List.length_cons,List.length_nil,hlen,Nat.cast_add,Nat.cast_ofNat]
    dsimp [pos]
    push_cast
    omega
  have hreverse' : downHolds t (pos-2) (ys.reverse ++ [false,false]) := by
    have hw : ([false,false] ++ ys).reverse=ys.reverse ++ [false,false] := by simp
    rw [hstart,hw] at hreverse
    exact hreverse
  have hrev_u : downHolds u (pos-2) (ys.reverse ++ [false,false]) := by
    apply downHolds_of_left_frame t u pos (pos-2) _ (by omega)
    · intro q hq
      simp [u,clearAt,show q≠pos by omega]
    · exact hreverse'
  have hys_u : Holds u (h+11) (ys ++ [false]) := by
    apply holds_transport t u _ _ hyEnd
    intro q hq hq'
    simp [u,clearAt,show q≠pos by
      simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one,hlen] at hq'
      dsimp [pos] at *
      omega]
  have hlast : Holds u (h+11+((ys ++ [false]).length : Int)) [false] := by
    have he : h+11+((ys ++ [false]).length : Int)=pos := by
      simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one,hlen]
      dsimp [pos]
      push_cast
      omega
    rw [he]
    simp [u,clearAt,Holds]
  have hforward := holds_append_intro u (h+11) (ys ++ [false]) [false] hys_u hlast
  refine ⟨prefix_unaryBank r values,reverse_prefix_generic r values,hrev_u,?_,?_⟩
  · change Holds u (h+11) (ys ++ [false,false])
    simpa [List.append_assoc] using hforward
  · change pos=(h+8)+(ys.length : Int)+4
    rw [hlen]
    dsimp [pos]
    push_cast
    omega

#print axioms windows
end Shared.Beeping.NPcoNP.NativeIncrementWindowGeneric
