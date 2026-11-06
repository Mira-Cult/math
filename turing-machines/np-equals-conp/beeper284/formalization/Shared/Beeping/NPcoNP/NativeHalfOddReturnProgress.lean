import Shared.Beeping.NPcoNP.NativeHalfOddReturn
import Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
import Shared.Beeping.NPcoNP.NativeHalfAllResiduals

/-! A left-zero tail supplies the finite delimiter for the odd return scan.
The resulting progress theorem applies to every prepared odd loop size,
without assuming that the blank-start machine reaches its input boundary. -/
namespace Shared.Beeping.NPcoNP.NativeHalfOddReturnProgress

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfOddReturn
open Shared.Beeping.NPcoNP.NativeHalfOddToCleanup
open Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfRegularIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.NativeHalfAllResiduals
open Shared.Beeping.NPcoNP.UnarySuffixShift

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- A left-zero tail forces either odd-return scanner phase to finish in
at most `k+2` steps, preserving tape and emitting no beep. -/
theorem scan25_left_zero (k : Nat) (h : Int) (t : Int → Bool)
    (hz : ∀ p ≤ h-(k : Int), t p=false) :
    ∀ (phase : Bool), ∃ n : Nat, 0<n ∧ n≤k+2 ∧
      silentSegment machine (cfg (if phase then 26 else 25) h t) (cfg 95 (h-(n : Int)) t) n := by
  induction k generalizing h with
  | zero =>
    intro phase
    have h0 : t h=false := hz h (by simp)
    have h1 : t (h-1)=false := hz (h-1) (by simp)
    cases phase with
    | false =>
      refine ⟨2,by omega,by omega,?_⟩
      have ha := oneSeg machine _ _ (step25_zero h t h0)
      have hb := oneSeg machine _ _ (step26_zero (h-1) t h1)
      have he : h-1-1=h-2 := by omega
      simpa [he] using segAdd machine _ _ _ 1 1 ha hb
    | true =>
      refine ⟨1,by omega,by omega,?_⟩
      simpa using oneSeg machine _ _ (step26_zero h t h0)
  | succ k ih =>
    intro phase
    have hz' : ∀ p ≤ (h-1)-(k : Int), t p=false := by
      intro p hp
      apply hz p
      simp only [Nat.cast_succ] at *
      omega
    cases phase with
    | false =>
      cases hv : t h with
      | false =>
        obtain ⟨n,hn,hbound,hs⟩ := ih (h-1) hz' true
        refine ⟨1+n,by omega,by omega,?_⟩
        have he : h-1-(n : Int)=h-((1+n : Nat) : Int) := by push_cast; omega
        simpa [he] using segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step25_zero h t hv)) hs
      | true =>
        obtain ⟨n,hn,hbound,hs⟩ := ih (h-1) hz' false
        refine ⟨1+n,by omega,by omega,?_⟩
        have he : h-1-(n : Int)=h-((1+n : Nat) : Int) := by push_cast; omega
        simpa [he] using segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step25_one h t hv)) hs
    | true =>
      cases hv : t h with
      | false =>
        refine ⟨1,by omega,by omega,?_⟩
        simpa using oneSeg machine _ _ (step26_zero h t hv)
      | true =>
        obtain ⟨n,hn,hbound,hs⟩ := ih (h-1) hz' false
        refine ⟨1+n,by omega,by omega,?_⟩
        have he : h-1-(n : Int)=h-((1+n : Nat) : Int) := by push_cast; omega
        simpa [he] using segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step26_one h t hv)) hs

/-- Every visit of the blank-start run to state 25 has a finite silent
continuation to state 95. This does not establish such a visit. -/
theorem reachable_25_progress (time : Nat) (hs : (machine.system.run time).state=25) :
    ∃ (n : Nat) (endHead : Int), 0<n ∧
      silentSegment machine (machine.system.run time)
        (cfg 95 endHead (machine.system.run time).tape) n := by
  obtain ⟨z,hz⟩ := run_has_left_zero time
  let c := machine.system.run time
  let k := (c.head-min z c.head).toNat
  have hk : c.head-(k : Int)≤z := by
    have hn : 0≤c.head-min z c.head := by omega
    have he : (k : Int)=c.head-min z c.head := Int.toNat_of_nonneg hn
    omega
  have ht : ∀ p ≤ c.head-(k : Int), c.tape p=false := by
    intro p hp
    exact hz p (le_trans hp hk)
  obtain ⟨n,hn,_,hseg⟩ := scan25_left_zero k c.head c.tape ht false
  have hc : c=cfg 25 c.head c.tape := by
    have he : c=cfg c.state c.head c.tape := by cases c; rfl
    have hs' : c.state=25 := hs
    simpa only [hs'] using he
  refine ⟨n,c.head-(n : Int),hn,?_⟩
  simpa [← hc] using hseg

/-- The accumulated boundary writes leave every cell strictly left of the
original boundary unchanged, independently of the number of iterations. -/
theorem bases_left (base : Int → Bool) (b p : Int) (i : Nat) (hp : p<b) :
    bases base b i p=base p := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [bases]
    rw [put_other _ _ _ _ (by simp [boundary]; omega),ih]

/-- The size-one residual also reaches state 95 when its base has a
left-zero tail. -/
theorem residual_one_to95_of_tail (base : Int → Bool) (g z : Int) (xs : List Nat)
    (hz : ∀ p ≤ z, base p=false) :
    ∃ (n : Nat) (endHead : Int), 0<n ∧ endHead<g ∧
      silentSegment machine (cfg 30 g (after base g (UnaryBank.encode (0::xs))))
        (cfg 95 endHead (postTape (put base g true) g xs)) n := by
  let t := postTape (put base g true) g xs
  have ht : ∀ p ≤ min z (g-1), t p=false := by
    intro p hp
    have hpz : p≤z := le_trans hp (min_le_left _ _)
    have hpg : p≤g-1 := le_trans hp (min_le_right _ _)
    change postTape (put base g true) g xs p=false
    rw [postTape_prefix _ _ _ _ (by omega),put_other _ _ _ _ (by omega)]
    exact hz p hpz
  let d := (g-min (min z (g-1)) g).toNat
  have hd : g-(d : Int)≤min z (g-1) := by
    have hn : 0≤g-min (min z (g-1)) g := by omega
    have he : (d : Int)=g-min (min z (g-1)) g := Int.toNat_of_nonneg hn
    omega
  have ht' : ∀ p ≤ g-(d : Int), t p=false := by
    intro p hp
    exact ht p (le_trans hp hd)
  obtain ⟨n,hn,_,hr⟩ := scan25_left_zero d g t ht' false
  have hc := residual_one_through_cleanup base g xs
  change silentSegment machine _ (cfg 25 g t) _ at hc
  refine ⟨(2*(UnaryBank.encode xs).length+10)+n,g-(n : Int),by omega,by omega,?_⟩
  exact segAdd machine _ _ _ _ _ hc hr

/-- A finite left-zero tail suffices for the whole prepared odd loop and
return. The complete post-cleanup tape is retained at state 95. -/
theorem maximal_odd_to95_of_tail (base : Int → Bool) (b z : Int) (m : Nat)
    (xs : List Nat) (hb : base b=true) (hm : 3≤m) (hodd : m%2=1)
    (hz : ∀ p ≤ z, base p=false) :
    let k := regularCount m-1
    let g := boundary b k+1
    let bs := bases base b k
    let vs := tailValues xs k
    ∃ (n : Nat) (endHead : Int), 0<n ∧ endHead<g ∧
      silentSegment machine
        (cfg 30 (boundary b 0)
          (prior (bases base b 0) (boundary b 0) (suffix (value m) (tailValues xs) 0)))
        (cfg 95 endHead (postTape (put bs g true) g vs)) n := by
  dsimp only
  let k := regularCount m-1
  let g := boundary b k+1
  let bs := bases base b k
  let vs := tailValues xs k
  let t := postTape (put bs g true) g vs
  have htail : ∀ p ≤ min z (b-1), t p=false := by
    intro p hp
    have hpz : p≤z := le_trans hp (min_le_left _ _)
    have hpb : p≤b-1 := le_trans hp (min_le_right _ _)
    have hpg : p≤g := by dsimp [g,boundary]; omega
    have hne : p≠g := by dsimp [g,boundary]; omega
    change postTape (put bs g true) g vs p=false
    rw [postTape_prefix _ _ _ _ hpg,put_other _ _ _ _ hne]
    change bases base b k p=false
    rw [bases_left base b p k (by omega)]
    exact hz p hpz
  let d := (g-min (min z (b-1)) g).toNat
  have hd : g-(d : Int)≤min z (b-1) := by
    have hn : 0≤g-min (min z (b-1)) g := by omega
    have he : (d : Int)=g-min (min z (b-1)) g := Int.toNat_of_nonneg hn
    omega
  have ht : ∀ p ≤ g-(d : Int), t p=false := by
    intro p hp
    exact htail p (le_trans hp hd)
  obtain ⟨n,hn,_,hreturn⟩ := scan25_left_zero d g t ht false
  have hclean := maximal_odd_through_cleanup base b m xs hb hm hodd
  dsimp only at hclean
  change silentSegment machine _ (cfg 25 g t) _ at hclean
  let clean := totalDuration (value m) (tailValues xs) k + duration (value m) (tailValues xs) k +
    3 + (2*(UnaryBank.encode vs).length+7)
  refine ⟨clean+n,g-(n : Int),by omega,?_,?_⟩
  · change g-(n : Int)<g
    omega
  · exact segAdd machine _ _ _ _ _ hclean hreturn

/-- All odd prepared right-block sizes finish their literal HALF loop,
cleanup and return to state 95 when the base has a left-zero tail. The
entire tape strictly left of the initial boundary is preserved. -/
theorem prepared_odd_to95 (base : Int → Bool) (b z : Int) (m : Nat)
    (xs : List Nat) (hodd : m%2=1) (hz : ∀ p ≤ z, base p=false) :
    ∃ (n : Nat) (endHead : Int) (t : Int → Bool), 0<n ∧
      (∀ p<b, t p=base p) ∧
      silentSegment machine (cfg 30 b (prepared base b m xs)) (cfg 95 endHead t) n := by
  by_cases h1 : m=1
  · subst m
    obtain ⟨n,p,hn,_,hs⟩ := residual_one_to95_of_tail base b z xs hz
    refine ⟨n,p,postTape (put base b true) b xs,hn,?_,?_⟩
    · intro q hq
      rw [postTape_prefix _ _ _ _ (by omega),put_other _ _ _ _ (by omega)]
    · simpa only [prepared_one] using hs
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
    obtain ⟨n,p,hn,_,hs⟩ := maximal_odd_to95_of_tail base' b (min z (b-1)) m (xs++[0]) hb hm hodd hz'
    let k := regularCount m-1
    let g := boundary b k+1
    let bs := bases base' b k
    let vs := tailValues (xs++[0]) k
    let t := postTape (put bs g true) g vs
    refine ⟨n,p,t,hn,?_,?_⟩
    · intro q hq
      have hqg : q≤g := by dsimp [g,boundary]; omega
      have hne : q≠g := by dsimp [g,boundary]; omega
      change postTape (put bs g true) g vs q=base q
      rw [postTape_prefix _ _ _ _ hqg,put_other _ _ _ _ hne]
      change bases base' b k q=base q
      rw [bases_left base' b q k hq]
      exact put_other base b q true (by omega)
    · change silentSegment machine (cfg 30 b (prepared base b m xs)) (cfg 95 p t) n
      have hs' : silentSegment machine
          (cfg 30 b (prior base' b (UnaryBank.encode ((m-3)::(xs++[0]))))) (cfg 95 p t) n := by
        simpa only [t,bs,g,k,vs,bases,boundary,suffix,value,tailValues,List.replicate_zero,List.append_nil,
          Nat.cast_zero,Int.add_zero,Nat.mul_zero,Nat.sub_zero] using hs
      rw [prepared_large base b m xs hm]
      exact hs'

end Shared.Beeping.NPcoNP.NativeHalfOddReturnProgress

#print axioms Shared.Beeping.NPcoNP.NativeHalfOddReturnProgress.reachable_25_progress
#print axioms Shared.Beeping.NPcoNP.NativeHalfOddReturnProgress.maximal_odd_to95_of_tail
#print axioms Shared.Beeping.NPcoNP.NativeHalfOddReturnProgress.prepared_odd_to95
