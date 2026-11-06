import Shared.Beeping.NPcoNP.NativeHalfOddReturnProgress

/-! The odd return scanner stops at a genuine double-zero delimiter. The
second-phase premise records the zero read immediately before that phase. -/
namespace Shared.Beeping.NPcoNP.NativeHalfOddReturnPair

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfOddReturn
open Shared.Beeping.NPcoNP.NativeHalfOddToCleanup
open Shared.Beeping.NPcoNP.NativeHalfOddReturnProgress
open Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfRegularIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.UnarySuffixShift

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- The output head lies immediately left of two zeros, and the tape is
unchanged. This strengthens finite progress with the delimiter's location. -/
theorem scan25_zero_pair (k : Nat) (h : Int) (t : Int → Bool)
    (hz : ∀ p≤h-(k : Int), t p=false) :
    ∀ phase : Bool, (phase=true → t (h+1)=false) →
      ∃ n : Nat, 0<n ∧ n≤k+2 ∧ t (h-(n : Int)+1)=false ∧
        t (h-(n : Int)+2)=false ∧
        silentSegment machine (cfg (if phase then 26 else 25) h t)
          (cfg 95 (h-(n : Int)) t) n := by
  induction k generalizing h with
  | zero =>
    intro phase hprev
    have h0 : t h=false := hz h (by simp)
    have h1 : t (h-1)=false := hz (h-1) (by simp)
    cases phase with
    | false =>
      refine ⟨2,by omega,by omega,?_,?_,?_⟩
      · have he : h-2+1=h-1 := by omega
        simpa [he] using h1
      · simpa using h0
      · have ha := oneSeg machine _ _ (step25_zero h t h0)
        have hb := oneSeg machine _ _ (step26_zero (h-1) t h1)
        have he : h-1-1=h-2 := by omega
        simpa [he] using segAdd machine _ _ _ 1 1 ha hb
    | true =>
      refine ⟨1,by omega,by omega,?_,?_,?_⟩
      · simpa using h0
      · have he : h-1+2=h+1 := by omega
        simpa [he] using hprev rfl
      · simpa using oneSeg machine _ _ (step26_zero h t h0)
  | succ k ih =>
    intro phase hprev
    have hz' : ∀ p≤(h-1)-(k : Int), t p=false := by
      intro p hp
      apply hz p
      simp only [Nat.cast_succ] at *
      omega
    cases phase with
    | false =>
      cases hv : t h with
      | false =>
        obtain ⟨n,hn,hbound,hz0,hz1,hs⟩ := ih (h-1) hz' true (by intro _; simpa using hv)
        refine ⟨1+n,by omega,by omega,?_,?_,?_⟩
        · have he : (h-1)-(n : Int)+1=h-((1+n : Nat) : Int)+1 := by push_cast; omega
          rw [← he]; exact hz0
        · have he : (h-1)-(n : Int)+2=h-((1+n : Nat) : Int)+2 := by push_cast; omega
          rw [← he]; exact hz1
        · have he : (h-1)-(n : Int)=h-((1+n : Nat) : Int) := by push_cast; omega
          simpa [he] using segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step25_zero h t hv)) hs
      | true =>
        obtain ⟨n,hn,hbound,hz0,hz1,hs⟩ := ih (h-1) hz' false (by simp)
        refine ⟨1+n,by omega,by omega,?_,?_,?_⟩
        · have he : (h-1)-(n : Int)+1=h-((1+n : Nat) : Int)+1 := by push_cast; omega
          rw [← he]; exact hz0
        · have he : (h-1)-(n : Int)+2=h-((1+n : Nat) : Int)+2 := by push_cast; omega
          rw [← he]; exact hz1
        · have he : (h-1)-(n : Int)=h-((1+n : Nat) : Int) := by push_cast; omega
          simpa [he] using segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step25_one h t hv)) hs
    | true =>
      cases hv : t h with
      | false =>
        refine ⟨1,by omega,by omega,?_,?_,?_⟩
        · simpa using hv
        · have he : h-1+2=h+1 := by omega
          simpa [he] using hprev rfl
        · simpa using oneSeg machine _ _ (step26_zero h t hv)
      | true =>
        obtain ⟨n,hn,hbound,hz0,hz1,hs⟩ := ih (h-1) hz' false (by simp)
        refine ⟨1+n,by omega,by omega,?_,?_,?_⟩
        · have he : (h-1)-(n : Int)+1=h-((1+n : Nat) : Int)+1 := by push_cast; omega
          rw [← he]; exact hz0
        · have he : (h-1)-(n : Int)+2=h-((1+n : Nat) : Int)+2 := by push_cast; omega
          rw [← he]; exact hz1
        · have he : (h-1)-(n : Int)=h-((1+n : Nat) : Int) := by push_cast; omega
          simpa [he] using segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step26_one h t hv)) hs

/-- A cleanup tape with a left-zero base reaches the double-zero delimiter
without modifying its tape, and exposes the delimiter relative to the
state-95 head. -/
theorem postTape_return_pair (base : Int → Bool) (g z : Int) (xs : List Nat)
    (hz : ∀ p≤z, base p=false) :
    ∃ (n : Nat) (head : Int), 0<n ∧ head<g ∧
      postTape base g xs (head+1)=false ∧ postTape base g xs (head+2)=false ∧
      silentSegment machine (cfg 25 g (postTape base g xs))
        (cfg 95 head (postTape base g xs)) n := by
  let t := postTape base g xs
  let d := (g-min z g).toNat
  have hd : g-(d : Int)≤z ∧ g-(d : Int)≤g := by
    have hn : 0≤g-min z g := by omega
    have he : (d : Int)=g-min z g := Int.toNat_of_nonneg hn
    omega
  have ht : ∀ p≤g-(d : Int), t p=false := by
    intro p hp
    change postTape base g xs p=false
    rw [postTape_prefix _ _ _ _ (by omega)]
    exact hz p (by omega)
  obtain ⟨n,hn,_,h0,h1,hseg⟩ := scan25_zero_pair d g t ht false (by simp)
  exact ⟨n,g-(n : Int),hn,by omega,h0,h1,hseg⟩

theorem residual_one_to95_pair (base : Int → Bool) (g z : Int) (xs : List Nat)
    (hz : ∀ p≤z, base p=false) :
    ∃ (n : Nat) (head : Int), 0<n ∧ head<g ∧
      postTape (put base g true) g xs (head+1)=false ∧
      postTape (put base g true) g xs (head+2)=false ∧
      silentSegment machine (cfg 30 g (after base g (UnaryBank.encode (0::xs))))
        (cfg 95 head (postTape (put base g true) g xs)) n := by
  have hz' : ∀ p≤min z (g-1), put base g true p=false := by
    intro p hp
    have hpz : p≤z := le_trans hp (min_le_left _ _)
    have hpg : p≤g-1 := le_trans hp (min_le_right _ _)
    rw [put_other _ _ _ _ (by omega)]
    exact hz p hpz
  obtain ⟨n,head,hn,hh,h0,h1,hr⟩ := postTape_return_pair (put base g true) g (min z (g-1)) xs hz'
  have hc := residual_one_through_cleanup base g xs
  refine ⟨(2*(UnaryBank.encode xs).length+10)+n,head,by omega,hh,h0,h1,?_⟩
  exact segAdd machine _ _ _ _ _ hc hr

theorem maximal_odd_to95_pair (base : Int → Bool) (b z : Int) (m : Nat) (xs : List Nat)
    (hb : base b=true) (hm : 3≤m) (hodd : m%2=1) (hz : ∀ p≤z, base p=false) :
    let k := regularCount m-1
    let g := boundary b k+1
    let bs := bases base b k
    let vs := tailValues xs k
    ∃ (n : Nat) (head : Int), 0<n ∧ head<g ∧
      postTape (put bs g true) g vs (head+1)=false ∧
      postTape (put bs g true) g vs (head+2)=false ∧
      silentSegment machine
        (cfg 30 (boundary b 0)
          (prior (bases base b 0) (boundary b 0) (suffix (value m) (tailValues xs) 0)))
        (cfg 95 head (postTape (put bs g true) g vs)) n := by
  dsimp only
  let k := regularCount m-1
  let g := boundary b k+1
  let bs := bases base b k
  let vs := tailValues xs k
  have hz' : ∀ p≤min z (b-1), put bs g true p=false := by
    intro p hp
    have hpz : p≤z := le_trans hp (min_le_left _ _)
    have hpb : p≤b-1 := le_trans hp (min_le_right _ _)
    have hne : p≠g := by dsimp [g,boundary]; omega
    rw [put_other _ _ _ _ hne]
    change bases base b k p=false
    rw [bases_left base b p k (by omega)]
    exact hz p hpz
  obtain ⟨n,head,hn,hh,h0,h1,hr⟩ := postTape_return_pair (put bs g true) g (min z (b-1)) vs hz'
  have hc := maximal_odd_through_cleanup base b m xs hb hm hodd
  dsimp only at hc
  change silentSegment machine _ (cfg 25 g (postTape (put bs g true) g vs)) _ at hc
  let clean := totalDuration (value m) (tailValues xs) k + duration (value m) (tailValues xs) k +
    3 + (2*(UnaryBank.encode vs).length+7)
  refine ⟨clean+n,head,by omega,?_,h0,h1,?_⟩
  · change head<g
    exact hh
  · exact segAdd machine _ _ _ _ _ hc hr

end Shared.Beeping.NPcoNP.NativeHalfOddReturnPair

#print axioms Shared.Beeping.NPcoNP.NativeHalfOddReturnPair.scan25_zero_pair
#print axioms Shared.Beeping.NPcoNP.NativeHalfOddReturnPair.postTape_return_pair
#print axioms Shared.Beeping.NPcoNP.NativeHalfOddReturnPair.residual_one_to95_pair
#print axioms Shared.Beeping.NPcoNP.NativeHalfOddReturnPair.maximal_odd_to95_pair
