import Shared.Beeping.NPcoNP.NativeManyForward
import Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
import Shared.Beeping.NPcoNP.NativeIncReturn23
import Shared.Beeping.NPcoNP.NativeHalfZeroPrefix

/-! Complete finite forward/backward suffix traversal for the literal
many-selector branch. The supplied double-zero boundary forces progress. -/
namespace Shared.Beeping.NPcoNP.NativeManyComplete
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncReturn23
open Shared.Beeping.NPcoNP.NativeManyShift
open Shared.Beeping.NPcoNP.NativeManySelectorReturn
open Shared.Beeping.NPcoNP.NativeManySweep
open Shared.Beeping.NPcoNP.NativeManyForward
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Reversing any zero-pair-free shape, with one delimiter prepended and one
marker appended, is again a legal backward-sweep shape. -/
theorem reverse_shape_prefix (s : Shape) :
    Prefix ([false] ++ (bits s).reverse ++ [true]) := by
  induction s with
  | stop => exact .zeroOne .nil
  | one s ih =>
    have he : [false] ++ (bits (Shape.one s)).reverse ++ [true] =
        ([false] ++ (bits s).reverse ++ [true]) ++ [true] := by simp [bits,List.append_assoc]
    rw [he]
    exact prefix_append ih (.one .nil)
  | zeroOne s ih =>
    have he : [false] ++ (bits (Shape.zeroOne s)).reverse ++ [true] =
        ([false] ++ (bits s).reverse ++ [true]) ++ [false,true] := by simp [bits,List.append_assoc]
    rw [he]
    exact prefix_append ih (.zeroOne .nil)

/-- The temporary first-cell clear has no effect on the final simultaneous
shift, because the sweep reads only cells strictly to its right. -/
theorem clear_start_irrelevant (t : Int → Bool) (x : Int) (n : Nat) :
    spec (clearAt x t) (x+2+(n : Int)) (n+2) =
      spec t (x+2+(n : Int)) (n+2) := by
  funext p
  simp only [spec,clearAt,Nat.cast_add,Nat.cast_ofNat]
  split_ifs <;> simp_all <;> omega

/-- Starting at the first of two supplied ones, the many-selector branch
traverses any finite zero-pair-free suffix, shifts its full interval, and
returns to state 23 in exactly twice the suffix length plus eight silent
steps. The two zeroes at each end guarantee positive finite completion. -/
theorem complete_shift (s : Shape) (x : Int) (t : Int → Bool)
    (left : t (x-1)=false)
    (word : Holds t x (true :: true :: (bits s ++ [false,false]))) :
    silentSegment machine (cfg 13 x t)
      (cfg 23 (x-2) (spec t (x+2+(bits s).length) ((bits s).length+2)))
      (2*(bits s).length+8) := by
  let u := clearAt x t
  let w := [true] ++ bits s ++ [false]
  let v := [false] ++ (bits s).reverse ++ [true]
  let f := x+2+((bits s).length : Int)
  have hfirst : t x=true := word.1
  have hsecond : u (x+1)=true := by
    simp [u,clearAt,show x+1≠x by omega,word.2.1]
  have hfull : Holds u (x+1) (true :: (bits s ++ [false,false])) := by
    apply holds_clear_left t x (x+1) _ (by omega)
    exact word.2
  have hfwd : Holds u (x+2) (bits s ++ [false,false]) := by
    have hp : x+1+1=x+2 := by omega
    simpa only [Holds,hp] using hfull.2
  have hw : Holds u (x+1) w := by
    apply holds_prefix_word u (x+1) w [false]
    simpa [w,List.append_assoc] using hfull
  have hreverse := holds_reverse u (x+1) w hw
  have hv : downHolds u f v := by
    have hf : x+1+(w.length : Int)-1=f := by
      simp [w,f]
      omega
    rw [hf] at hreverse
    simpa [w,v,List.reverse_append,List.append_assoc] using hreverse
  have hlen : v.length=(bits s).length+2 := by simp [v]
  have hz : downHolds u (f-(v.length : Int)) [false,false] := by
    have hf : f-(v.length : Int)=x := by rw [hlen]; dsimp [f]; push_cast; omega
    rw [hf]
    simp [downHolds,u,clearAt,show x-1≠x by omega,left]
  have hvall := down_append u f v [false,false] hv hz
  obtain ⟨back,hback⟩ := shape_of_prefix v (reverse_shape_prefix s)
  have hd : downHolds u f (bits back ++ [false,false]) := by rw [hback]; exact hvall
  have hbl : (bits back).length=(bits s).length+2 := by rw [hback,hlen]
  have hforward := scan18 s (x+2) u hfwd
  have hbackward := sweep20_spec back f u hd
  have hstate13 := oneSeg machine _ _ (step13_1 x t hfirst)
  have hstate17 := oneSeg machine _ _ (step17_1 (x+1) u hsecond)
  have hpre : silentSegment machine (cfg 13 x t) (cfg 18 (x+2) u) 2 := by
    simpa [u,Int.add_assoc] using segAdd machine _ _ _ 1 1 hstate13 hstate17
  have hmid := segAdd machine _ _ _ 2 ((bits s).length+2) hpre hforward
  have hmid' : silentSegment machine (cfg 13 x t) (cfg 20 f u) (2+((bits s).length+2)) := by
    simpa [f] using hmid
  rw [hbl] at hbackward
  have hall := segAdd machine _ _ _ (2+((bits s).length+2)) ((bits s).length+2+2) hmid' hbackward
  have hp : f-(((bits s).length+2 : Nat) : Int)-2=x-2 := by dsimp [f]; push_cast; omega
  have hc : 2+((bits s).length+2)+((bits s).length+2+2)=2*(bits s).length+8 := by omega
  have he : spec u f ((bits s).length+2)=spec t f ((bits s).length+2) := by
    exact clear_start_irrelevant t x (bits s).length
  simpa only [hp,hc,he,f] using hall

/-- List-based version of the complete shift, using the shared prefix
predicate for an arbitrary finite zero-pair-free suffix. -/
theorem complete_shift_prefix (xs : List Bool) (hp : Prefix xs)
    (x : Int) (t : Int → Bool) (left : t (x-1)=false)
    (word : Holds t x (true :: true :: (xs ++ [false,false]))) :
    silentSegment machine (cfg 13 x t)
      (cfg 23 (x-2) (spec t (x+2+xs.length) (xs.length+2))) (2*xs.length+8) := by
  obtain ⟨s,hs⟩ := shape_of_prefix xs hp
  have hw : Holds t x (true :: true :: (bits s ++ [false,false])) := by rw [hs]; exact word
  have h := complete_shift s x t left hw
  simpa only [hs] using h

/-- Every nonempty unary bank whose first value is positive satisfies the
finite-suffix precondition. The ordinary final separator and one extra blank
supply the required double-zero end. -/
theorem complete_shift_bank (v : Nat) (vs : List Nat) (x : Int) (t : Int → Bool)
    (left : t (x-1)=false)
    (bank : Holds t x (UnaryBank.encode ((v+1)::vs) ++ [false])) :
    let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
    silentSegment machine (cfg 13 x t)
      (cfg 23 (x-2) (spec t (x+2+suffix.length) (suffix.length+2))) (2*suffix.length+8) := by
  dsimp only
  let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
  have hp : Prefix suffix := prefix_tail_unary v vs
  have hb := bank
  rw [← bank_prefix_identity (v+1) vs] at hb
  have hw : Holds t x (true :: true :: (suffix ++ [false,false])) := by
    simpa [unaryBankPrefix,suffix,List.replicate_succ,Nat.add_assoc,List.cons_append] using hb
  exact complete_shift_prefix suffix hp x t left hw

/-- Complete the state-15 branch over arbitrary delimited initial scans
and any supplied finite nonempty encoded bank whose first value is positive. -/
theorem scans_then_bank (p n v : Nat) (vs : List Nat) (h : Int) (t : Int → Bool)
    (first : Holds t h (List.replicate p true ++ [false]))
    (second : Holds t (h+(p : Int)+1) (List.replicate n true ++ [false]))
    (left : t (h+(p : Int)+(n : Int)+1)=false)
    (bank : Holds t (h+(p : Int)+(n : Int)+2)
      (UnaryBank.encode ((v+1)::vs) ++ [false])) :
    let x := h+(p : Int)+(n : Int)+2
    let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
    silentSegment machine (cfg 15 h t)
      (cfg 23 (x-2) (spec t (x+2+suffix.length) (suffix.length+2)))
      (p+n+2*suffix.length+10) := by
  dsimp only
  let x := h+(p : Int)+(n : Int)+2
  let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
  have hs1 := scan15 p h t first
  have hs2 := scan11 n (h+(p : Int)+1) t second
  have hc : x-1=h+(p : Int)+(n : Int)+1 := by dsimp [x]; omega
  have hleft : t (x-1)=false := by rw [hc]; exact left
  have hs3 := complete_shift_bank v vs x t hleft bank
  have h12 := segAdd machine _ _ _ (p+1) (n+1) hs1 hs2
  have h12' : silentSegment machine (cfg 15 h t) (cfg 13 x t) (p+1+(n+1)) := by
    have he : h+(p : Int)+1+(n : Int)+1=x := by dsimp [x]; omega
    simpa only [he] using h12
  have hall := segAdd machine _ _ _ (p+1+(n+1)) (2*suffix.length+8) h12' hs3
  have hd : p+1+(n+1)+(2*suffix.length+8)=p+n+2*suffix.length+10 := by omega
  simpa only [hd,x,suffix] using hall

#print axioms reverse_shape_prefix
#print axioms clear_start_irrelevant
#print axioms complete_shift
#print axioms complete_shift_bank
#print axioms scans_then_bank
end Shared.Beeping.NPcoNP.NativeManyComplete
