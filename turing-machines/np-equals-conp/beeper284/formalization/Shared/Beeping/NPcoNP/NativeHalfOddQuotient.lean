import Shared.Beeping.NPcoNP.NativeHalfOddReturnPair
import Shared.Beeping.NPcoNP.NativeHalfOddBankDecode

/-! Identify the physical quotient block for a prepared odd residual. The
left block is an explicit input condition; blank-start reachability and the
connection to a graph-level HALF operand remain separate. -/
namespace Shared.Beeping.NPcoNP.NativeHalfOddQuotient

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfAllResiduals
open Shared.Beeping.NPcoNP.NativeHalfOddReturnProgress
open Shared.Beeping.NPcoNP.NativeHalfOddReturnPair
open Shared.Beeping.NPcoNP.NativeHalfOddBank
open Shared.Beeping.NPcoNP.NativeHalfCleanupBank
open Shared.Beeping.NPcoNP.NativeHalfRegularIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfOddFinish
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Strengthen the bank return with the actual double-zero delimiter at the
state-95 head. The counted suffix excludes the final `after` reserve. -/
theorem prepared_odd_to95_bank_pair (base : Int → Bool) (b z : Int) (m : Nat)
    (xs : List Nat) (hodd : m%2=1) (hz : ∀ p≤z, base p=false) :
    ∃ (n : Nat) (head gap : Int) (outBase : Int → Bool), 0<n ∧ b≤gap ∧
      gap=b+(((m-1)/2 : Nat) : Int) ∧ head<gap ∧
      (∀ p<b, outBase p=base p) ∧ (∀ p, b≤p → p≤gap → outBase p=true) ∧
      let word := encode (xs ++ List.replicate ((m+1)/2) 0)
      (after outBase (gap+1) word) (head+1)=false ∧
      (after outBase (gap+1) word) (head+2)=false ∧
      silentSegment machine (cfg 30 b (prepared base b m xs))
        (cfg 95 head (after outBase (gap+1) word)) n := by
  by_cases h1 : m=1
  · subst m
    obtain ⟨n,h,hn,hh,h0,h2,hs⟩ := residual_one_to95_pair base b z xs hz
    rw [postTape_as_bank] at h0 h2 hs
    refine ⟨n,h,b,put base b true,hn,by omega,by simp,hh,?_,?_,?_,?_,?_⟩
    · intro p hp
      exact put_other base b p true (by omega)
    · intro p hp hp'
      have he : p=b := by omega
      subst p
      simp [put]
    · simpa only [show (1+1)/2=1 by decide,List.replicate_succ,List.replicate_zero] using h0
    · simpa only [show (1+1)/2=1 by decide,List.replicate_succ,List.replicate_zero] using h2
    · simpa only [prepared_one,show (1+1)/2=1 by decide,List.replicate_succ,
        List.replicate_zero] using hs
  · have hm : 3≤m := by omega
    let base' := put base b true
    have hb : base' b=true := by simp [base',put]
    have hz' : ∀ p≤min z (b-1), base' p=false := by
      intro p hp
      have hpz : p≤z := le_trans hp (min_le_left _ _)
      have hpb : p≤b-1 := le_trans hp (min_le_right _ _)
      change put base b true p=false
      rw [put_other _ _ _ _ (by omega)]
      exact hz p hpz
    obtain ⟨n,h,hn,hh,h0,h2,hs⟩ := maximal_odd_to95_pair base' b (min z (b-1)) m
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
    rw [postTape_as_bank] at h0 h2 hs
    change (after outBase (gap+1) (encode (tailValues (xs++[0]) k ++ [0]))) (h+1)=false at h0
    change (after outBase (gap+1) (encode (tailValues (xs++[0]) k ++ [0]))) (h+2)=false at h2
    rw [hbank] at h0 h2
    refine ⟨n,h,gap,outBase,hn,by dsimp [gap,boundary]; omega,hgap,hh,hprefix,hfilled,h0,h2,?_⟩
    have hs' : silentSegment machine
        (cfg 30 b (prior base' b (encode ((m-3)::(xs++[0])))))
        (cfg 95 h (after outBase (gap+1) (encode (xs ++ List.replicate ((m+1)/2) 0)))) n := by
      change silentSegment machine _ (cfg 95 h
        (after outBase (gap+1) (encode (tailValues (xs++[0]) k ++ [0])))) n at hs
      rw [hbank] at hs
      simpa only [bases,boundary,suffix,value,tailValues,List.replicate_zero,List.append_nil,
        Nat.cast_zero,Int.add_zero,Nat.mul_zero,Nat.sub_zero] using hs
    rw [prepared_large base b m xs hm]
    exact hs'

/-- For a prepared odd residual with a nonempty left block, the literal
table completes silently to state 1. It leaves the selected block encoding
the arithmetic quotient and the supplied suffix decoding to its original
values followed by the counted zero blocks. The separately appended reserve
is also present. This does not establish that an actual graph call reaches
this prepared layout. -/
theorem prepared_odd_quotient_and_bank (base : Int → Bool) (b z : Int) (a m : Nat)
    (xs : List Nat) (ha : 1≤a) (hodd : m%2=1)
    (hz : ∀ p≤z, base p=false)
    (hleft : ∀ p, b-(a : Int)≤p → p<b → base p=true) :
    ∃ (n₁ n₂ : Nat) (head gap : Int) (finalTape : Int → Bool),
      0<n₁ ∧ 0<n₂ ∧ b≤gap ∧
      Holds finalTape (b-(a : Int)) (block (sourceValue a m / 2)) ∧
      let values := xs ++ List.replicate ((m+1)/2) 0
      let word := encode values
      decode (xs.length+(m+1)/2) (readCells finalTape (gap+2) word.length)=some (values,[]) ∧
      finalTape (gap+2+(word.length : Int))=true ∧
      finalTape (gap+3+(word.length : Int))=false ∧
      silentSegment machine (cfg 30 b (prepared base b m xs))
        (cfg 1 (head-(n₂ : Int)) finalTape) (n₁+n₂) := by
  obtain ⟨n₁,head,gap,outBase,hn₁,hbg,hgap,hhead,hprefix,hfilled,hzero,_,hfirst⟩ :=
    prepared_odd_to95_bank_pair base b z m xs hodd hz
  let values := xs ++ List.replicate ((m+1)/2) 0
  let word := encode values
  let t := after outBase (gap+1) word
  have hsafe : head<b-(a : Int) := by
    by_contra hn
    have hlo : b-(a : Int)≤head+1 := by omega
    have hhi : head+1≤gap := by omega
    have hp : t (head+1)=true := by
      change after outBase (gap+1) word (head+1)=true
      rw [after_prefix _ _ _ _ (by omega)]
      by_cases hb : head+1<b
      · rw [hprefix _ hb]
        exact hleft _ hlo hb
      · exact hfilled _ (by omega) hhi
    change t (head+1)=false at hzero
    rw [hp] at hzero
    contradiction
  let left := min z (b-1)
  let k := (head-min left head).toNat
  have hk : head-(k : Int)≤left := by
    have hn : 0≤head-min left head := by omega
    have he : (k : Int)=head-min left head := Int.toNat_of_nonneg hn
    omega
  have ht : t (head-(k : Int))=false := by
    have hza : left≤z := min_le_left _ _
    have hba : left≤b-1 := min_le_right _ _
    change after outBase (gap+1) word (head-(k : Int))=false
    rw [after_prefix _ _ _ _ (by omega),hprefix _ (by omega)]
    exact hz _ (by omega)
  obtain ⟨n₂,hn₂,_,hsecond⟩ := scan95_exact k head t ht
  let finalTape := clearRange t (head-(n₂ : Int)+2) (head+1)
  have hquot : Holds finalTape (b-(a : Int)) (block (sourceValue a m / 2)) :=
    quotient_block_of_safe_return base outBase b gap head a m n₂ word ha hodd hgap hleft hprefix hfilled hsafe
  have hout : ∀ p≥gap+1, finalTape p=t p := by
    intro p hp
    have hn : ¬ (head-(n₂ : Int)+2≤p ∧ p<head+1) := by omega
    change (if head-(n₂ : Int)+2≤p ∧ p<head+1 then false else t p)=t p
    rw [if_neg hn]
  have hbits : ∀ i : Nat, i<word.length → finalTape (gap+2+(i : Int))=bitAt word i := by
    intro i hi
    rw [hout _ (by omega)]
    have h := after_suffix_bit outBase (gap+1) word i hi
    simpa only [Int.add_assoc,show (1 : Int)+1=2 by decide] using h
  have hreserve0 : finalTape (gap+2+(word.length : Int))=true := by
    rw [hout _ (by omega)]
    have h := (appended_zero_block outBase (gap+1) word).1
    simpa only [Int.add_assoc,show (1 : Int)+1=2 by decide] using h
  have hreserve1 : finalTape (gap+3+(word.length : Int))=false := by
    rw [hout _ (by omega)]
    have h := (appended_zero_block outBase (gap+1) word).2
    simpa only [Int.add_assoc,show (1 : Int)+2=3 by decide] using h
  have hh : Holds finalTape (gap+2) word := by
    apply holds_of_get
    intro i hi
    have h := hbits i hi
    simpa only [bitAt,List.getElem?_eq_getElem hi,Option.getD_some] using h
  have hr := read_of_holds finalTape (gap+2) word hh
  have hd : decode (xs.length+(m+1)/2) word=some (values,[]) := by
    have h := decode_encode values []
    simpa only [List.append_nil,values,List.length_append,List.length_replicate] using h
  refine ⟨n₁,n₂,head,gap,finalTape,hn₁,hn₂,hbg,hquot,?_,hreserve0,hreserve1,?_⟩
  · rw [hr]
    exact hd
  · exact segAdd machine _ _ _ n₁ n₂ hfirst hsecond

end Shared.Beeping.NPcoNP.NativeHalfOddQuotient

#print axioms Shared.Beeping.NPcoNP.NativeHalfOddQuotient.prepared_odd_to95_bank_pair
#print axioms Shared.Beeping.NPcoNP.NativeHalfOddQuotient.prepared_odd_quotient_and_bank
