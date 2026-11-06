import Shared.Beeping.NPcoNP.NativeHalfOddQuotient

/-! The odd residual reaches the literal state-25 return scanner with its
full suffix and filled boundary described. This is a prepared local input. -/
namespace Shared.Beeping.NPcoNP.NativeHalfPrepared25Bank

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfAllResiduals
open Shared.Beeping.NPcoNP.NativeHalfOddToCleanup
open Shared.Beeping.NPcoNP.NativeHalfOddReturnProgress
open Shared.Beeping.NPcoNP.NativeHalfOddBank
open Shared.Beeping.NPcoNP.NativeHalfCleanupBank
open Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
open Shared.Beeping.NPcoNP.NativeHalfRegularIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Every odd residual reaches state 25 after finite silent cleanup; the
gap, filled cells and original suffix are explicit. -/
theorem prepared_odd_to25_bank (base : Int → Bool) (b : Int) (m : Nat)
    (xs : List Nat) (hodd : m%2=1) :
    ∃ (n : Nat) (gap : Int) (outBase : Int → Bool), 0<n ∧
      gap=b+(((m-1)/2 : Nat) : Int) ∧
      (∀ p<b, outBase p=base p) ∧ (∀ p, b≤p → p≤gap → outBase p=true) ∧
      silentSegment machine (cfg 30 b (prepared base b m xs))
        (cfg 25 gap (after outBase (gap+1) (encode (xs ++ List.replicate ((m+1)/2) 0)))) n := by
  by_cases h1 : m=1
  · subst m
    have hs := residual_one_through_cleanup base b xs
    rw [postTape_as_bank] at hs
    refine ⟨2*(encode xs).length+10,b,put base b true,by omega,by simp,?_,?_,?_⟩
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
    let k := regularCount m-1
    let gap := boundary b k+1
    let outBase := put (bases base' b k) gap true
    let vs := tailValues (xs++[0]) k
    let clean := totalDuration (value m) (tailValues (xs++[0])) k +
      duration (value m) (tailValues (xs++[0])) k + 3 + (2*(encode vs).length+7)
    have hs := maximal_odd_through_cleanup base' b m (xs++[0]) hb hm hodd
    dsimp only at hs
    change silentSegment machine _ (cfg 25 gap (postTape outBase gap vs)) clean at hs
    rw [postTape_as_bank] at hs
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
    have hbank : vs ++ [0] = xs ++ List.replicate ((m+1)/2) 0 := by
      dsimp [vs]
      rw [tail_reserve_count,hcount]
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
    rw [hbank] at hs
    refine ⟨clean,gap,outBase,by dsimp [clean]; omega,hgap,hprefix,hfilled,?_⟩
    have hs' : silentSegment machine
        (cfg 30 b (prior base' b (encode ((m-3)::(xs++[0])))))
        (cfg 25 gap (after outBase (gap+1) (encode (xs ++ List.replicate ((m+1)/2) 0)))) clean := by
      simpa only [bases,boundary,suffix,value,tailValues,List.replicate_zero,List.append_nil,
        Nat.cast_zero,Int.add_zero,Nat.mul_zero,Nat.sub_zero] using hs
    rw [prepared_large base b m xs hm]
    exact hs'

end Shared.Beeping.NPcoNP.NativeHalfPrepared25Bank

#print axioms Shared.Beeping.NPcoNP.NativeHalfPrepared25Bank.prepared_odd_to25_bank
