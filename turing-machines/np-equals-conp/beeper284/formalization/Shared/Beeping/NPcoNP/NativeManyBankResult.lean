import Shared.Beeping.NPcoNP.NativeManyComplete
import Shared.Beeping.NPcoNP.NativeIncBank

/-! Interpret the complete literal shift as decrementing the first positive
unary value and appending one zero-valued reserve, with an exact tape frame. -/
namespace Shared.Beeping.NPcoNP.NativeManyBankResult
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeManyComplete
open Shared.Beeping.NPcoNP.NativeManySelectorReturn
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

/-- An asserted word shifted across the interior of the pointwise tape
specification retains every bit in order. -/
theorem holds_spec_interval (t : Int → Bool) (f : Int) (k : Nat)
    (a : Int) (xs : List Bool)
    (lo : f-(k : Int)≤a) (hi : a+(xs.length : Int)≤f)
    (hw : Holds t (a+1) xs) : Holds (spec t f k) a xs := by
  induction xs generalizing a with
  | nil => trivial
  | cons b xs ih =>
    change t (a+1)=b ∧ Holds t (a+1+1) xs at hw
    change spec t f k a=b ∧ Holds (spec t f k) (a+1) xs
    have ha : a<f := by simp only [List.length_cons,Nat.cast_succ] at hi; omega
    constructor
    · rw [spec_inside t f a k lo ha]; exact hw.1
    · apply ih (a+1) (by omega) (by simp only [List.length_cons,Nat.cast_succ] at hi; omega)
      simpa [Int.add_assoc] using hw.2

/-- The finite shift removes the leading one and appends `10`; the
additional supplied zero is preserved as the trailing blank. -/
theorem rotate_word (t : Int → Bool) (x : Int) (xs : List Bool)
    (word : Holds t (x+1) (xs ++ [false])) :
    Holds (spec t (x+(xs.length : Int)) xs.length) x (xs ++ [true,false]) := by
  let f := x+(xs.length : Int)
  have hx : Holds t (x+1) xs := holds_prefix_word t (x+1) xs [false] word
  have hw : Holds (spec t f xs.length) x xs := by
    apply holds_spec_interval t f xs.length x xs
    · dsimp [f]; omega
    · dsimp [f]; omega
    · exact hx
  have ht := holds_append_tail t (x+1) xs [false] word
  have hb : t (f+1)=false := by
    have he : x+1+(xs.length : Int)=f+1 := by dsimp [f]; omega
    rw [he] at ht
    exact ht.1
  have htail : Holds (spec t f xs.length) (x+(xs.length : Int)) [true,false] := by
    change spec t f xs.length f=true ∧ spec t f xs.length (f+1)=false ∧ True
    refine ⟨spec_top t f xs.length,?_,trivial⟩
    rw [spec_outside t f (f+1) xs.length (Or.inr (by omega))]
    exact hb
  exact holds_append_intro (spec t f xs.length) x xs [true,false] hw htail

/-- The complete physical segment changes the first encoded value from
`v+1` to `v` and adds one zero-valued reserve. Every cell outside the
finite shifted interval is unchanged. -/
theorem shift_bank_result (v : Nat) (vs : List Nat) (x : Int) (t : Int → Bool)
    (left : t (x-1)=false)
    (bank : Holds t x (encode ((v+1)::vs) ++ [false])) :
    let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
    let f := x+2+suffix.length
    let out := spec t f (suffix.length+2)
    Holds out x (encode (v::vs) ++ [true,false]) ∧
    (∀ p, p<x ∨ f<p → out p=t p) ∧
    silentSegment machine (cfg 13 x t) (cfg 23 (x-2) out) (2*suffix.length+8) := by
  dsimp only
  let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
  let f := x+2+((suffix.length : Nat):Int)
  let out := spec t f (suffix.length+2)
  have htail : Holds t (x+1) (encode (v::vs) ++ [false]) := by
    have h := bank.2
    simpa [encode,block,List.replicate_succ,Nat.add_assoc,List.cons_append] using h
  have hlen : (encode (v::vs)).length=suffix.length+2 := by
    have h := prefix_length v vs
    simp only [unaryBankPrefix,List.length_append,List.length_replicate,
      List.length_flatMap] at h
    dsimp [suffix]
    simp only [List.length_append,List.length_replicate,List.length_flatMap]
    omega
  have hf : x+((encode (v::vs)).length : Int)=f := by rw [hlen]; dsimp [f]; push_cast; omega
  have hrot := rotate_word t x (encode (v::vs)) htail
  rw [hf,hlen] at hrot
  have hframe : ∀ p, p<x ∨ f<p → out p=t p := by
    intro p hp
    apply spec_outside
    dsimp [f] at hp ⊢
    push_cast
    omega
  refine ⟨hrot,hframe,?_⟩
  exact complete_shift_bank v vs x t left bank

/-- Include the two preceding paid scans, preserving the bank-level result
and the full-tape frame from the physical state-15 entry. -/
theorem scans_then_bank_result (p n v : Nat) (vs : List Nat) (h : Int) (t : Int → Bool)
    (first : Holds t h (List.replicate p true ++ [false]))
    (second : Holds t (h+(p : Int)+1) (List.replicate n true ++ [false]))
    (left : t (h+(p : Int)+(n : Int)+1)=false)
    (bank : Holds t (h+(p : Int)+(n : Int)+2) (encode ((v+1)::vs) ++ [false])) :
    let x := h+(p : Int)+(n : Int)+2
    let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
    let f := x+2+suffix.length
    let out := spec t f (suffix.length+2)
    Holds out x (encode (v::vs) ++ [true,false]) ∧
    (∀ z, z<x ∨ f<z → out z=t z) ∧
    silentSegment machine (cfg 15 h t) (cfg 23 (x-2) out) (p+n+2*suffix.length+10) := by
  dsimp only
  let x := h+(p : Int)+(n : Int)+2
  have hx : x-1=h+(p : Int)+(n : Int)+1 := by dsimp [x]; omega
  have hleft : t (x-1)=false := by rw [hx]; exact left
  obtain ⟨hbank,hframe,_⟩ := shift_bank_result v vs x t hleft bank
  exact ⟨hbank,hframe,scans_then_bank p n v vs h t first second left bank⟩

/-- If a second blank was supplied after the input bank, the appended
reserve is followed by a blank as well. This additional hypothesis is needed
for a later scan that requires a double-zero end. -/
theorem shift_bank_with_blank (v : Nat) (vs : List Nat) (x : Int) (t : Int → Bool)
    (left : t (x-1)=false)
    (bank : Holds t x (encode ((v+1)::vs) ++ [false,false])) :
    let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
    let f := x+2+suffix.length
    let out := spec t f (suffix.length+2)
    Holds out x (encode (v::vs) ++ [true,false,false]) ∧
    (∀ p, p<x ∨ f<p → out p=t p) ∧
    silentSegment machine (cfg 13 x t) (cfg 23 (x-2) out) (2*suffix.length+8) := by
  dsimp only
  let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
  let f := x+2+((suffix.length : Nat):Int)
  let out := spec t f (suffix.length+2)
  have bank' : Holds t x (encode ((v+1)::vs) ++ [false]) := by
    apply holds_prefix_word t x (encode ((v+1)::vs) ++ [false]) [false]
    simpa [List.append_assoc] using bank
  obtain ⟨hresult,hframe,hseg⟩ := shift_bank_result v vs x t left bank'
  change Holds out x (encode (v::vs) ++ [true,false]) at hresult
  change ∀ p, p<x ∨ f<p → out p=t p at hframe
  change silentSegment machine (cfg 13 x t) (cfg 23 (x-2) out) (2*suffix.length+8) at hseg
  change Holds out x (encode (v::vs) ++ [true,false,false]) ∧
    (∀ p, p<x ∨ f<p → out p=t p) ∧
    silentSegment machine (cfg 13 x t) (cfg 23 (x-2) out) (2*suffix.length+8)
  have hlen : (encode (v::vs)).length=suffix.length+2 := by
    have h := prefix_length v vs
    simp only [unaryBankPrefix,List.length_append,List.length_replicate,List.length_flatMap] at h
    dsimp [suffix]
    simp only [List.length_append,List.length_replicate,List.length_flatMap]
    omega
  have hlen' : (encode ((v+1)::vs)).length=suffix.length+3 := by
    have h := prefix_length (v+1) vs
    simp only [unaryBankPrefix,List.length_append,List.length_replicate,List.length_flatMap] at h
    dsimp [suffix]
    simp only [List.length_append,List.length_replicate,List.length_flatMap]
    omega
  have htail := holds_append_tail t x (encode ((v+1)::vs)) [false,false] bank
  have ht : t (f+2)=false := by
    have he : x+((encode ((v+1)::vs)).length : Int)+1=f+2 := by rw [hlen']; dsimp [f]; push_cast; omega
    have hh := htail.2.1
    rw [he] at hh
    exact hh
  have hout : out (f+2)=false := by rw [hframe _ (Or.inr (by omega))]; exact ht
  have hend : x+((encode (v::vs) ++ [true,false]).length : Int)=f+2 := by
    simp only [List.length_append,List.length_cons,List.length_nil]
    rw [hlen]
    dsimp [f]
    push_cast
    omega
  have hlast : Holds out (x+((encode (v::vs) ++ [true,false]).length : Int)) [false] := by
    rw [hend]
    exact ⟨hout,trivial⟩
  have hall := holds_append_intro out x (encode (v::vs) ++ [true,false]) [false] hresult hlast
  refine ⟨?_,hframe,hseg⟩
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using hall

/-- The same prepared-bank segment has an exact linear physical cost in
the full input bank length, including all separators. -/
theorem shift_bank_linear_cost (v : Nat) (vs : List Nat) (x : Int) (t : Int → Bool)
    (left : t (x-1)=false)
    (bank : Holds t x (encode ((v+1)::vs) ++ [false,false])) :
    let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
    let f := x+2+suffix.length
    let out := spec t f (suffix.length+2)
    Holds out x (encode (v::vs) ++ [true,false,false]) ∧
    (∀ p, p<x ∨ f<p → out p=t p) ∧
    silentSegment machine (cfg 13 x t) (cfg 23 (x-2) out)
      (2*(encode ((v+1)::vs)).length+2) := by
  dsimp only
  let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
  have hlen : (encode ((v+1)::vs)).length=suffix.length+3 := by
    have h := prefix_length (v+1) vs
    simp only [unaryBankPrefix,List.length_append,List.length_replicate,List.length_flatMap] at h
    dsimp [suffix]
    simp only [List.length_append,List.length_replicate,List.length_flatMap]
    omega
  have hcost : 2*suffix.length+8=2*(encode ((v+1)::vs)).length+2 := by rw [hlen]; omega
  have h := shift_bank_with_blank v vs x t left bank
  dsimp only at h
  rw [hcost] at h
  exact h

#print axioms rotate_word
#print axioms shift_bank_result
#print axioms scans_then_bank_result
#print axioms shift_bank_with_blank
#print axioms shift_bank_linear_cost
end Shared.Beeping.NPcoNP.NativeManyBankResult
