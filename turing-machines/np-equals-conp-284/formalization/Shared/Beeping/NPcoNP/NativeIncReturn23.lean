import Shared.Beeping.NPcoNP.NativeIncSelected
import Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
import Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
import Shared.Beeping.NPcoNP.NativeHalfReturn23

/-! Exact literal state-23 return across a supplied encoded bank and header.
This does not assert that the supplied layout occurs in the actual run. -/
namespace Shared.Beeping.NPcoNP.NativeIncReturn23
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
open Shared.Beeping.NPcoNP.NativeHalfReturn23
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

theorem prefix_tail_after_zero (xs : List Bool) (h : Prefix (false::xs)) : Prefix xs := by
  cases h with
  | zeroOne h => exact Prefix.one h

theorem down_append (t : Int → Bool) (h : Int) (xs ys : List Bool)
    (hx : downHolds t h xs) (hy : downHolds t (h-(xs.length : Int)) ys) :
    downHolds t h (xs++ys) := by
  induction xs generalizing h with
  | nil => simpa using hy
  | cons x xs ih =>
    change t h=x ∧ downHolds t (h-1) xs at hx
    change t h=x ∧ downHolds t (h-1) (xs++ys)
    refine ⟨hx.1,ih (h-1) hx.2 ?_⟩
    simpa [Int.sub_sub,Int.add_assoc,Int.add_comm,Int.add_left_comm] using hy

/-- State 23 traverses a complete nonempty bank backwards to its supplied
zero-zero header, without writing or beeping. -/
theorem encoded_bank_to1 (v : Nat) (rest : List Nat) (base : Int) (t : Int → Bool)
    (bank : Holds t base (encode (v::rest)))
    (hleft1 : t (base-1)=false) (hleft2 : t (base-2)=false) :
    silentSegment machine (cfg 23 (base+((encode (v::rest)).length : Int)-2) t)
      (cfg 1 (base-3) t) ((encode (v::rest)).length+1) := by
  obtain ⟨word,hword⟩ := encode_ends_zero (v::rest) (by simp)
  have hlen : (encode (v::rest)).length=word.length+1 := by rw [hword]; simp
  have hp : Prefix (false::word.reverse) := by
    have hh := prefix_reverse_bank (v::rest)
    rw [hword] at hh
    simpa using hh
  obtain ⟨shape,hshape⟩ := shape_of_prefix word.reverse (prefix_tail_after_zero _ hp)
  have hprefix : Holds t base word := by
    have hh : Holds t base (word++[false]) := by rw [←hword]; exact bank
    exact holds_prefix t base word [false] hh
  have hreverse := holds_reverse t base word hprefix
  have hzeros : downHolds t (base-1) [false,false] := by
    change t (base-1)=false ∧ t (base-1-1)=false ∧ True
    have he : base-1-1=base-2 := by omega
    exact ⟨hleft1,by rw [he]; exact hleft2,trivial⟩
  have hpad : downHolds t (base+(word.length : Int)-1) (word.reverse++[false,false]) := by
    apply down_append t _ word.reverse [false,false] hreverse
    have he : base+(word.length : Int)-1-(word.reverse.length : Int)=base-1 := by simp; omega
    rw [he]
    exact hzeros
  rw [← hshape] at hpad
  have hseg := return_scan shape (base+(word.length : Int)-1) t hpad
  have hshapeLen : (bits shape).length=word.length := by rw [hshape]; simp
  have hstart : base+(word.length : Int)-1=base+((encode (v::rest)).length : Int)-2 := by
    rw [hlen]; push_cast; omega
  have hend : base+(word.length : Int)-1-((bits shape).length : Int)-2=base-3 := by
    rw [hshapeLen]; omega
  have hcost : (bits shape).length+2=(encode (v::rest)).length+1 := by rw [hshapeLen,hlen]
  rw [hend,hstart,hcost] at hseg
  exact hseg

/-- Exact increment of a selected value followed by an exact backward scan
to the left of the two-zero header. The supplied tape layout need not be
asserted reachable here. -/
theorem selected_increment_to1 (prior rest : List Nat) (v : Nat)
    (base : Int) (t : Int → Bool)
    (bank : Holds t base (encode (prior ++ v::rest) ++ [false]))
    (hleft1 : t (base-1)=false) (hleft2 : t (base-2)=false) :
    let h := base+((encode prior).length : Int)
    let values := prior ++ (v+1)::rest
    ∃ mid : Config 284, mid.state=23 ∧
      Holds mid.tape base (encode values) ∧
      (∀ p<h, mid.tape p=t p) ∧
      silentSegment machine (cfg 14 h t) mid (v+3+(encode rest).length) ∧
      silentSegment machine mid (cfg 1 (base-3) mid.tape) ((encode values).length+1) := by
  dsimp only
  let h := base+((encode prior).length : Int)
  let values := prior ++ (v+1)::rest
  have whole : Holds t base (encode prior ++ (encode (v::rest) ++ [false])) := by
    simpa [encode_append,List.append_assoc] using bank
  have hprefix : Holds t base (encode prior) := holds_prefix t base _ _ whole
  have hselected : Holds t h (encode (v::rest) ++ [false]) := by
    exact holds_append_tail t base (encode prior) (encode (v::rest) ++ [false]) whole
  obtain ⟨mid,h23,hhead,hout,hframe,hseg⟩ := encoded_increment v rest h t hselected
  have hprefix' : Holds mid.tape base (encode prior) := by
    apply holds_transport t mid.tape base (encode prior) hprefix
    intro p hlo hhi
    symm
    apply hframe p
    left
    exact hhi
  have hbank : Holds mid.tape base (encode values) := by
    have hh := holds_append_intro mid.tape base (encode prior) (encode ((v+1)::rest)) hprefix' hout
    simpa [values,encode_append] using hh
  have hn : (0:Int)≤(encode prior).length := by omega
  have hp1 : base-1<h := by dsimp [h]; omega
  have hp2 : base-2<h := by dsimp [h]; omega
  have hh1 : mid.tape (base-1)=false := by
    rw [hframe _ (Or.inl hp1)]
    exact hleft1
  have hh2 : mid.tape (base-2)=false := by
    rw [hframe _ (Or.inl hp2)]
    exact hleft2
  have hvalues : values≠[] := by dsimp [values]; simp
  obtain ⟨x,xs,hvalues'⟩ := List.exists_cons_of_ne_nil hvalues
  have hlast : mid.head=base+((encode values).length : Int)-2 := by
    rw [hhead]
    dsimp [h,values]
    simp only [encode_append,List.length_append,encode,block_length,Nat.cast_add]
    push_cast
    omega
  have hmid : mid=cfg 23 mid.head mid.tape := by
    have hh : mid=cfg mid.state mid.head mid.tape := by cases mid; rfl
    simpa only [h23] using hh
  have hb : Holds mid.tape base (encode (x::xs)) := by rw [←hvalues']; exact hbank
  have hreturn := encoded_bank_to1 x xs base mid.tape hb hh1 hh2
  rw [←hvalues',←hlast,←hmid] at hreturn
  exact ⟨mid,h23,hbank,fun p hp => hframe p (Or.inl hp),hseg,hreturn⟩

#print axioms selected_increment_to1
#print axioms encoded_bank_to1
end Shared.Beeping.NPcoNP.NativeIncReturn23
