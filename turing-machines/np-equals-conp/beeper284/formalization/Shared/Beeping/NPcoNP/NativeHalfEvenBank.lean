import Shared.Beeping.NPcoNP.NativeHalfEvenCleanup
import Shared.Beeping.NPcoNP.NativeHalfAllResiduals
import Shared.Beeping.NPcoNP.NativeHalfCleanupBank
import Shared.Beeping.NPcoNP.NativeHalfOddBank

/-! The prepared even-residual HALF path through state 23, with its full
unary suffix and reserve count. Entry reachability and the later return are
separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeHalfEvenBank

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfAllResiduals
open Shared.Beeping.NPcoNP.NativeHalfEvenCleanup
open Shared.Beeping.NPcoNP.NativeHalfEvenIterations
open Shared.Beeping.NPcoNP.NativeHalfExceptionalCycle
open Shared.Beeping.NPcoNP.NativeHalfCleanupComposed
open Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
open Shared.Beeping.NPcoNP.NativeHalfCleanupBank
open Shared.Beeping.NPcoNP.NativeHalfZeroResidual
open Shared.Beeping.NPcoNP.NativeHalfOddBank
open Shared.Beeping.NPcoNP.NativeHalfOddReturnProgress
open Shared.Beeping.NPcoNP.NativeHalfRegularIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopIteration
open Shared.Beeping.NPcoNP.NativeHalfMaximalIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

theorem even_reserve_count (m : Nat) (hm : 3≤m) (he : m%2=0) :
    (regularCount m-1)+3=m/2+1 := by
  simp only [regularCount]
  omega

theorem even_tail_reserves (xs : List Nat) (k : Nat) :
    (tailValues (xs++[0]) k ++ [0]) ++ [0] = xs ++ List.replicate (k+3) 0 := by
  rw [tail_reserve_count]
  rw [List.append_assoc,← List.replicate_succ']

/-- Every prepared even right-block size reaches state 23 silently. Its
suffix is unchanged with `m/2+1` zero blocks appended inside the encoded
bank; `after` supplies its separate final `10` reserve. -/
theorem prepared_even_to23_bank (base : Int → Bool) (b : Int) (m : Nat)
    (xs : List Nat) (he : m%2=0) :
    ∃ (n : Nat) (gap : Int) (outBase : Int → Bool), 0<n ∧
      gap=b+((m/2 : Nat) : Int)-1 ∧
      (∀ p<b, outBase p=base p) ∧ (∀ p, b≤p → p≤gap → outBase p=true) ∧
      silentSegment machine (cfg 30 b (prepared base b m xs))
        (cfg 23 gap (after outBase (gap+1) (encode (xs ++ List.replicate (m/2+1) 0)))) n := by
  by_cases h0 : m=0
  · subst m
    obtain ⟨hz0,hz1⟩ := prepared_zero base b xs
    have hfirst := zero_residual b (prepared base b 0 xs) hz0 hz1
    have heq : NativeHalfAllResiduals.prepared base b 0 xs = after base b (false :: encode xs) := by
      simp [NativeHalfAllResiduals.prepared]
    rw [heq] at hfirst
    have hc := cleanup18 base b xs
    have h := segAdd machine _ _ _ 3 (2*(encode xs).length+8) hfirst hc
    rw [postTape_as_bank] at h
    refine ⟨3+(2*(encode xs).length+8),b-1,base,by omega,?_,?_,?_,?_⟩
    · simp
    · intro p hp; rfl
    · intro p hp hp'; omega
    · simpa only [heq,show (0 : Nat)/2+1=1 by decide,List.replicate_succ,List.replicate_zero,
        Int.sub_add_cancel] using h
  by_cases h2 : m=2
  · subst m
    let outBase := put base b true
    have hb : outBase b=true := by simp [outBase,put]
    obtain ⟨n,hn,h⟩ := exceptional_through_cleanup outBase b (xs++[0]) hb
    have h' : silentSegment machine
        (cfg 30 b (prior outBase b (false :: encode (xs++[0]))))
        (cfg 23 b (postTape outBase b (xs++[0]))) n := by
      simpa only [postTape] using h
    rw [postTape_as_bank] at h'
    refine ⟨n,b,outBase,hn,by simp,?_,?_,?_⟩
    · intro p hp
      exact put_other base b p true (by omega)
    · intro p hp hp'
      have hp'' : p=b := by omega
      subst p
      simp [outBase,put]
    · simpa only [prepared_two,show (2 : Nat)/2+1=2 by decide,List.replicate_succ,
        List.replicate_zero,List.append_assoc,List.cons_append,List.nil_append] using h'
  · have hm : 3≤m := by omega
    let base' := put base b true
    have hb : base' b=true := by simp [base',put]
    let k := regularCount m-1
    let gap := boundary b k+1
    let bs := bases base' b k
    let vs := tailValues (xs++[0]) k
    let outBase := put bs gap true
    have hcount : k+3=m/2+1 := even_reserve_count m hm he
    have hgap : gap=b+((m/2 : Nat) : Int)-1 := by
      dsimp [gap,boundary,k,regularCount]
      omega
    have hprefix : ∀ p<b, outBase p=base p := by
      intro p hp
      have hpg : p≠gap := by dsimp [gap,boundary]; omega
      change put (bases base' b k) gap true p=base p
      rw [put_other _ _ _ _ hpg,bases_left base' b p k hp]
      exact put_other base b p true (by omega)
    have hfilled : ∀ p, b≤p → p≤gap → outBase p=true := by
      intro p hpb hpg
      by_cases hp : p=gap
      · subst p; simp [outBase,put]
      · let j := (p-b).toNat
        have hjint : (j : Int)=p-b := by dsimp [j]; exact Int.toNat_of_nonneg (by omega)
        have hj : j≤k := by dsimp [gap,boundary] at hpg hp; omega
        have hp' : b+(j : Int)=p := by omega
        change put (bases base' b k) gap true p=true
        rw [put_other _ _ _ _ hp,← hp']
        exact bases_filled base b k j hj
    have hval : value m k=1 := by
      have hc : 0<regularCount m := (count_positive_iff m).2 hm
      have ht : m-2*regularCount m=2 := (terminal_two_iff m).2 ⟨by omega,he⟩
      simp only [value,k]
      omega
    have hiter := maximal_iterations base' b m (xs++[0]) hb hm
    dsimp only at hiter
    change silentSegment machine
      (cfg 30 (boundary b 0) (prior (bases base' b 0) (boundary b 0)
        (suffix (value m) (tailValues (xs++[0])) 0)))
      (cfg 30 gap (after bs gap (encode (value m k :: vs)))) _ at hiter
    rw [hval,residual_two_layout] at hiter
    obtain ⟨q,hq,hclean⟩ := exceptional_through_cleanup outBase gap (vs++[0]) (by simp [outBase,put])
    have hclean' : silentSegment machine (cfg 30 gap (prior outBase gap (false :: encode (vs++[0]))))
        (cfg 23 gap (postTape outBase gap (vs++[0]))) q := by simpa only [postTape] using hclean
    have htotal := segAdd machine _ _ _ _ q hiter hclean'
    rw [postTape_as_bank] at htotal
    have hbank : (vs++[0])++[0] = xs ++ List.replicate (m/2+1) 0 := by
      dsimp [vs]
      rw [even_tail_reserves,hcount]
    rw [hbank] at htotal
    let initial := totalDuration (value m) (tailValues (xs++[0])) k +
      duration (value m) (tailValues (xs++[0])) k
    refine ⟨initial+q,gap,outBase,by omega,hgap,hprefix,hfilled,?_⟩
    have hh : silentSegment machine (cfg 30 b (prior base' b (encode ((m-3)::(xs++[0])))))
        (cfg 23 gap (after outBase (gap+1) (encode (xs ++ List.replicate (m/2+1) 0)))) (initial+q) := by
      simpa only [bases,boundary,suffix,value,tailValues,List.replicate_zero,List.append_nil,
        Nat.cast_zero,Int.add_zero,Nat.mul_zero,Nat.sub_zero] using htotal
    rw [prepared_large base b m xs hm]
    exact hh

end Shared.Beeping.NPcoNP.NativeHalfEvenBank

#print axioms Shared.Beeping.NPcoNP.NativeHalfEvenBank.prepared_even_to23_bank
