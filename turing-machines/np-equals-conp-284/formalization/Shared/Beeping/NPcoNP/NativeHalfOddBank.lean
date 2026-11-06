import Shared.Beeping.NPcoNP.NativeHalfOddFinish
import Shared.Beeping.NPcoNP.NativeHalfCleanupBank
import Shared.Beeping.NPcoNP.Bootstrap284BankShape

/-! Bank-level postcondition for the prepared odd residual path. This
preserves the supplied suffix and counts appended zero blocks, but does not
identify the prepared residual with a complete graph-level HALF call. -/
namespace Shared.Beeping.NPcoNP.NativeHalfOddBank

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfAllResiduals
open Shared.Beeping.NPcoNP.NativeHalfOddReturnProgress
open Shared.Beeping.NPcoNP.NativeHalfOddFinish
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfCleanupBank
open Shared.Beeping.NPcoNP.NativeHalfRegularIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Bootstrap284BankShape

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

theorem tail_reserve_count (xs : List Nat) (k : Nat) :
    tailValues (xs ++ [0]) k ++ [0] = xs ++ List.replicate (k+2) 0 := by
  have hr : List.replicate (k+2) 0 = [0] ++ List.replicate k 0 ++ [0] := by
    calc
      List.replicate (k+2) 0 = List.replicate (1+k+1) 0 := by congr 1 <;> omega
      _ = List.replicate 1 0 ++ List.replicate k 0 ++ List.replicate 1 0 := by
        rw [← List.replicate_add,← List.replicate_add]
      _ = [0] ++ List.replicate k 0 ++ [0] := rfl
  rw [hr]
  simp [tailValues,List.append_assoc]

theorem odd_regular_reserve_count (m : Nat) (hm : 3≤m) (ho : m%2=1) :
    (regularCount m-1)+2=(m+1)/2 := by
  simp only [regularCount]
  omega

/-- In the loop's arithmetic model, an odd right residual gives an even
source value; the resulting encoded quotient block has this many ones. -/
theorem odd_residual_quotient_length (a m : Nat) (ha : 1≤a) (ho : m%2=1) :
    sourceValue a m % 2=0 ∧ sourceValue a m / 2 + 1 = a+(m+1)/2 := by
  simp only [sourceValue]
  omega

/-- The accumulated boundary writes create a contiguous run of ones from
the original boundary through the last regular-cycle boundary. -/
theorem bases_filled (base : Int → Bool) (b : Int) (k j : Nat) (hj : j≤k) :
    bases (put base b true) b k (b+(j : Int))=true := by
  induction k with
  | zero =>
    have h : j=0 := by omega
    subst j
    simp [bases,put]
  | succ k ih =>
    by_cases he : j=k+1
    · subst j
      simp [bases,boundary,put]
    · have hj' : j≤k := by omega
      have hn : b+(j : Int) ≠ boundary b (k+1) := by simp [boundary]; omega
      simp only [bases]
      rw [put_other _ _ _ _ hn]
      exact ih hj'

/-- The odd residual reaches state 95 with the original supplied suffix
unchanged and `(m+1)/2` zero blocks appended within the encoded suffix.
The `after` tape additionally has its final `10` reserve. The output base is
unchanged to the left of the original boundary. -/
theorem prepared_odd_to95_bank (base : Int → Bool) (b z : Int) (m : Nat)
    (xs : List Nat) (hodd : m%2=1) (hz : ∀ p ≤ z, base p=false) :
    ∃ (n : Nat) (head gap : Int) (outBase : Int → Bool), 0<n ∧ b≤gap ∧
      gap=b+(((m-1)/2 : Nat) : Int) ∧ head<gap ∧
      (∀ p<b, outBase p=base p) ∧ (∀ p, b≤p → p≤gap → outBase p=true) ∧
      silentSegment machine (cfg 30 b (prepared base b m xs))
        (cfg 95 head (after outBase (gap+1)
          (encode (xs ++ List.replicate ((m+1)/2) 0)))) n := by
  by_cases h1 : m=1
  · subst m
    obtain ⟨n,h,hn,hhead,hs⟩ := residual_one_to95_of_tail base b z xs hz
    rw [postTape_as_bank] at hs
    refine ⟨n,h,b,put base b true,hn,by omega,by simp,hhead,?_,?_,?_⟩
    · intro p hp
      exact put_other base b p true (by omega)
    · intro p hp hp'
      have he : p=b := by omega
      subst p
      simp [put]
    · simpa only [prepared_one,show (1+1)/2=1 by decide,List.replicate_succ,
        List.replicate_zero] using hs
  · have hm : 3≤m := by omega
    let base' := put base b true
    have hb : base' b=true := by simp [base',put]
    have hz' : ∀ p ≤ min z (b-1), base' p=false := by
      intro p hp
      have hpz : p≤z := le_trans hp (min_le_left _ _)
      have hpb : p≤b-1 := le_trans hp (min_le_right _ _)
      change put base b true p=false
      rw [put_other _ _ _ _ (by omega)]
      exact hz p hpz
    obtain ⟨n,h,hn,hhead,hs⟩ := maximal_odd_to95_of_tail base' b (min z (b-1)) m
      (xs++[0]) hb hm hodd hz'
    let k := regularCount m-1
    let gap := boundary b k+1
    let outBase := put (bases base' b k) gap true
    have hcount : k+2=(m+1)/2 := odd_regular_reserve_count m hm hodd
    have hgap : gap=b+(((m-1)/2 : Nat) : Int) := by
      dsimp [gap,boundary,k,regularCount]
      omega
    have hprefix : ∀ p<b, outBase p=base p := by
      intro p hp
      have hpg : p≠gap := by dsimp [gap,boundary]; omega
      change put (bases base' b k) gap true p=base p
      rw [put_other _ _ _ _ hpg,bases_left base' b p k hp]
      exact put_other base b p true (by omega)
    have hbank : tailValues (xs++[0]) k ++ [0] =
        xs ++ List.replicate ((m+1)/2) 0 := by rw [tail_reserve_count,hcount]
    have hfilled : ∀ p, b≤p → p≤gap → outBase p=true := by
      intro p hpb hpg
      by_cases he : p=gap
      · subst p
        simp [outBase,put]
      · let j := (p-b).toNat
        have hjint : (j : Int)=p-b := by dsimp [j]; exact Int.toNat_of_nonneg (by omega)
        have hj : j≤k := by dsimp [gap,boundary] at hpg he; omega
        have hp : b+(j : Int)=p := by omega
        change put (bases base' b k) gap true p=true
        rw [put_other _ _ _ _ he,← hp]
        exact bases_filled base b k j hj
    refine ⟨n,h,gap,outBase,by exact hn,by dsimp [gap,boundary]; omega,hgap,hhead,hprefix,hfilled,?_⟩
    have hs' : silentSegment machine
        (cfg 30 b (prior base' b (encode ((m-3)::(xs++[0])))))
        (cfg 95 h (after outBase (gap+1) (encode (xs ++ List.replicate ((m+1)/2) 0)))) n := by
      rw [postTape_as_bank] at hs
      change silentSegment machine _ (cfg 95 h
        (after outBase (gap+1) (encode (tailValues (xs++[0]) k ++ [0])))) n at hs
      rw [hbank] at hs
      simpa only [bases,boundary,suffix,value,tailValues,List.replicate_zero,List.append_nil,
        Nat.cast_zero,Int.add_zero,Nat.mul_zero,Nat.sub_zero] using hs
    rw [prepared_large base b m xs hm]
    exact hs'

/-- The state-95 cleanup stays left of the represented bank. Consequently
the original suffix, all counted added zero blocks, and the separate final
reserve remain readable after the odd path returns to state 1. -/
theorem prepared_odd_to1_bank (base : Int → Bool) (b z : Int) (m : Nat)
    (xs : List Nat) (hodd : m%2=1) (hz : ∀ p ≤ z, base p=false) :
    ∃ (n₁ n₂ : Nat) (head gap : Int) (outBase finalTape : Int → Bool),
      0<n₁ ∧ 0<n₂ ∧ b≤gap ∧ gap=b+(((m-1)/2 : Nat) : Int) ∧ head<gap ∧
      (∀ p<b, outBase p=base p) ∧ (∀ p, b≤p → p≤gap → outBase p=true) ∧
      let word := encode (xs ++ List.replicate ((m+1)/2) 0)
      finalTape = clearRange (after outBase (gap+1) word)
        (head-(n₂ : Int)+2) (head+1) ∧
      (∀ i : Nat, i<word.length → finalTape (gap+2+(i : Int))=bitAt word i) ∧
      finalTape (gap+2+(word.length : Int))=true ∧
      finalTape (gap+3+(word.length : Int))=false ∧
      silentSegment machine (cfg 30 b (prepared base b m xs))
        (cfg 1 (head-(n₂ : Int)) finalTape) (n₁+n₂) := by
  obtain ⟨n₁,head,gap,outBase,hn₁,hbg,hgap,hhead,hprefix,hfilled,hfirst⟩ :=
    prepared_odd_to95_bank base b z m xs hodd hz
  let word := encode (xs ++ List.replicate ((m+1)/2) 0)
  let t := after outBase (gap+1) word
  let a := min z (b-1)
  let k := (head-min a head).toNat
  have hk : head-(k : Int)≤a := by
    have hn : 0≤head-min a head := by omega
    have he : (k : Int)=head-min a head := Int.toNat_of_nonneg hn
    omega
  have ht : t (head-(k : Int))=false := by
    have hza : a≤z := min_le_left _ _
    have hba : a≤b-1 := min_le_right _ _
    have hb : head-(k : Int)<b := by omega
    have hg : head-(k : Int)<gap+1 := by omega
    change after outBase (gap+1) word (head-(k : Int))=false
    rw [after_prefix _ _ _ _ hg,hprefix _ hb]
    exact hz _ (by omega)
  obtain ⟨n₂,hn₂,_,hsecond⟩ := scan95_exact k head t ht
  let finalTape := clearRange t (head-(n₂ : Int)+2) (head+1)
  have hout : ∀ p ≥ gap+1, finalTape p=t p := by
    intro p hp
    have hn : ¬ (head-(n₂ : Int)+2≤p ∧ p<head+1) := by omega
    change (if head-(n₂ : Int)+2≤p ∧ p<head+1 then false else t p)=t p
    rw [if_neg hn]
  refine ⟨n₁,n₂,head,gap,outBase,finalTape,hn₁,hn₂,hbg,hgap,hhead,hprefix,hfilled,rfl,?_,?_,?_,?_⟩
  · intro i hi
    have hp : gap+1≤gap+2+(i : Int) := by omega
    rw [hout _ hp]
    have h := after_suffix_bit outBase (gap+1) word i hi
    simpa only [Int.add_assoc,show (1 : Int)+1=2 by decide] using h
  · have hp : gap+1≤gap+2+(word.length : Int) := by omega
    rw [hout _ hp]
    have h := (appended_zero_block outBase (gap+1) word).1
    simpa only [Int.add_assoc,show (1 : Int)+1=2 by decide] using h
  · have hp : gap+1≤gap+3+(word.length : Int) := by omega
    rw [hout _ hp]
    have h := (appended_zero_block outBase (gap+1) word).2
    simpa only [Int.add_assoc,show (1 : Int)+2=3 by decide] using h
  · exact segAdd machine _ _ _ n₁ n₂ hfirst hsecond

/-- If the state-95 head lies strictly left of the original left block,
its final clear cannot touch that block. Under this explicit physical
condition, the filled boundary encodes the arithmetic quotient. -/
theorem quotient_block_of_safe_return (base outBase : Int → Bool) (b gap head : Int)
    (a m n : Nat) (word : List Bool) (ha : 1≤a) (ho : m%2=1)
    (hgap : gap=b+(((m-1)/2 : Nat) : Int))
    (hleft : ∀ p, b-(a : Int)≤p → p<b → base p=true)
    (hprefix : ∀ p<b, outBase p=base p)
    (hfilled : ∀ p, b≤p → p≤gap → outBase p=true)
    (hsafe : head<b-(a : Int)) :
    Holds (clearRange (after outBase (gap+1) word) (head-(n : Int)+2) (head+1))
      (b-(a : Int)) (block (sourceValue a m / 2)) := by
  let start := b-(a : Int)
  let count := a+(m+1)/2
  let t := after outBase (gap+1) word
  let u := clearRange t (head-(n : Int)+2) (head+1)
  have hcount : sourceValue a m / 2+1=count := (odd_residual_quotient_length a m ha ho).2
  have hend : start+(count : Int)=gap+1 := by
    dsimp [start,count] at *
    omega
  have hsame : ∀ p ≥ start, u p=t p := by
    intro p hp
    have hn : ¬ (head-(n : Int)+2≤p ∧ p<head+1) := by dsimp [start] at hp; omega
    change (if head-(n : Int)+2≤p ∧ p<head+1 then false else t p)=t p
    rw [if_neg hn]
  have hones : Holds u start (List.replicate count true) := by
    apply holds_of_get
    intro i hi
    have hi' : i<count := by simpa using hi
    have hlo : start≤start+(i : Int) := by omega
    have hhi : start+(i : Int)≤gap := by omega
    rw [hsame _ hlo]
    change after outBase (gap+1) word (start+(i : Int)) = _
    rw [after_prefix _ _ _ _ (by omega)]
    by_cases hb : start+(i : Int)<b
    · rw [hprefix _ hb,hleft _ (by dsimp [start]; omega) hb]
      simp
    · rw [hfilled _ (by omega) hhi]
      simp
  have hsep : Holds u (start+count) [false] := by
    change u (start+(count : Int))=false ∧ True
    rw [hend,hsame _ (by omega)]
    exact ⟨(gap_cells outBase (gap+1) word).2.2, trivial⟩
  have hsep' : Holds u (start+((List.replicate count true).length : Int)) [false] := by
    simpa using hsep
  have hh := holds_append u start (List.replicate count true) [false] hones hsep'
  change Holds u start (block (sourceValue a m / 2))
  simpa [block,hcount] using hh

end Shared.Beeping.NPcoNP.NativeHalfOddBank

#print axioms Shared.Beeping.NPcoNP.NativeHalfOddBank.prepared_odd_to95_bank
#print axioms Shared.Beeping.NPcoNP.NativeHalfOddBank.prepared_odd_to1_bank
#print axioms Shared.Beeping.NPcoNP.NativeHalfOddBank.odd_residual_quotient_length
#print axioms Shared.Beeping.NPcoNP.NativeHalfOddBank.quotient_block_of_safe_return
