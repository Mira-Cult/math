import Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
import Shared.Beeping.NPcoNP.NativeHalfState93Progress

/-! The selector's nonempty marked window determines the first state-93
transition. This is conditional on the supplied tape window, not reachability. -/
namespace Shared.Beeping.NPcoNP.NativeHalfWindowDispatch

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState93Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfEntryCorrect
open Shared.Beeping.NPcoNP.NativeHalfEntryNonzero
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

/-- A nonempty reverse marker window starts with the final separator zero. -/
theorem marker_window_first_zero (xs : List Nat) (hne : xs ≠ []) :
    ∃ rest, markerWindow xs = false :: rest := by
  have hencode : encode xs ≠ [] := by
    cases xs with
    | nil => contradiction
    | cons x xs => simp [encode, block]
  have hlen : markerWindow xs ≠ [] := by
    intro h
    have he := markerWindow_append_zero xs
    rw [h] at he
    simp at he
    exact hencode he
  cases hw : markerWindow xs with
  | nil => exact False.elim (hlen hw)
  | cons b rest =>
    have he := markerWindow_append_zero xs
    rw [hw] at he
    have hb : b=false := by simpa using congrArg List.head? he
    subst b
    exact ⟨rest,rfl⟩

/-- The first separator is followed by a one from the first unary block. -/
theorem marker_window_prefix (xs : List Nat) (hne : xs ≠ []) :
    ∃ rest, markerWindow xs = false :: true :: rest := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
    obtain ⟨rest,hr⟩ := marker_window_first_zero (x::xs) (by simp)
    cases rest with
    | nil =>
      have he := markerWindow_append_zero (x::xs)
      rw [hr] at he
      simp [encode,block,List.replicate_succ] at he
    | cons b rest =>
      have he := markerWindow_append_zero (x::xs)
      rw [hr] at he
      simp [encode,block,List.replicate_succ] at he
      exact ⟨rest,by simpa [he.1] using hr⟩

/-- From the selector boundary, its marked window forces the silent zero
transition to state 6, retaining the entire tape. -/
theorem marker_window_step93 (t : Int → Bool) (a : Int) (xs : List Nat)
    (hne : xs ≠ []) (hw : Holds t a (markerWindow xs)) :
    silentSegment machine (cfg 93 a t) (cfg 6 (a+1) t) 1 := by
  obtain ⟨rest,he⟩ := marker_window_first_zero xs hne
  rw [he] at hw
  exact oneSeg machine _ _ (step93_zero a t hw.1)

/-- The exact output of a selector segment determines the next row and
preserves the same tape through that next silent transition. -/
theorem selected_window_to6 (back out : Int → Bool) (p : Int) (xs : List Nat)
    (start : Config 284) (n : Nat)
    (hl : xs.length=14)
    (hwin : Holds back (p-((encode xs).length : Int)) (markerWindow xs))
    (hprefix : ∀ q<p, out q=back q)
    (hseg : silentSegment machine start
      (cfg 93 (p-((encode xs).length : Int)) out) n) :
    silentSegment machine start
      (cfg 6 (p-((encode xs).length : Int)+1) out) (n+1) := by
  have hne : xs ≠ [] := by intro h; simp [h] at hl
  obtain ⟨rest,he⟩ := marker_window_first_zero xs hne
  have hlen : 0<(encode xs).length := by
    have hm := markerWindow_length xs
    rw [he] at hm
    simp at hm
    omega
  have hzero : out (p-((encode xs).length : Int))=false := by
    rw [hprefix _ (by omega)]
    rw [he] at hwin
    exact hwin.1
  exact segAdd machine _ _ _ n 1 hseg
    (oneSeg machine _ _ (step93_zero _ out hzero))

/-- The following window symbol is one, so state 6 takes its one row to
state 7 in one more silent step. -/
theorem selected_window_to7 (back out : Int → Bool) (p : Int) (xs : List Nat)
    (start : Config 284) (n : Nat)
    (hl : xs.length=14)
    (hwin : Holds back (p-((encode xs).length : Int)) (markerWindow xs))
    (hprefix : ∀ q<p, out q=back q)
    (hseg : silentSegment machine start
      (cfg 93 (p-((encode xs).length : Int)) out) n) :
    silentSegment machine start
      (cfg 7 (p-((encode xs).length : Int)+2) out) (n+2) := by
  have hne : xs ≠ [] := by intro h; simp [h] at hl
  obtain ⟨rest,he⟩ := marker_window_prefix xs hne
  have hlen : 1<(encode xs).length := by
    have hm := markerWindow_length xs
    rw [he] at hm
    simp at hm
    omega
  have hone : out (p-((encode xs).length : Int)+1)=true := by
    rw [hprefix _ (by omega)]
    rw [he] at hwin
    exact hwin.2.1
  have hs := selected_window_to6 back out p xs start n hl hwin hprefix hseg
  have hnext := oneSeg machine _ _ (step6_one _ out hone)
  have hr := segAdd machine _ _ _ (n+1) 1 hs hnext
  convert hr using 1 <;> congr 1 <;> omega

/-- Odd selected value: the literal table reaches state 6 with the exact
selector output tape after a strictly positive silent segment. -/
theorem selected_odd_entry_to6_exact (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right xs : List Nat) (k : Nat)
    (hz : ∀ p≤z, back p=false) (ho : value%2=1) (hl : xs.length=14)
    (hcarry : downHolds back (ctrl-1) (List.replicate k true ++ [false]))
    (hwin : Holds back (ctrl-1-(k : Int)-((encode xs).length : Int)) (markerWindow xs))
    (hleft : back (ctrl-1-(k : Int)-((encode xs).length : Int)-1)=true) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    let p := ctrl-1-(k : Int)
    let out := selectorOutputTape back ctrl value left right (ctrl-1) k
    ∃ n : Nat, 0<n ∧ out p=true ∧ (∀ q<p, out q=back q) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right))
        (cfg 6 (p-((encode xs).length : Int)+1) out) n := by
  dsimp only
  obtain ⟨n,hn,hm,hprefix,hseg⟩ :=
    selected_odd_entry_to93_exact back ctrl z value left right xs k hz ho hl hcarry hwin hleft
  refine ⟨n+1,by omega,hm,hprefix,?_⟩
  exact selected_window_to6 back _ _ xs _ n hl hwin hprefix hseg

/-- Even selected value: the same exact state-6 boundary, with the explicit
finite control run required by the even branch. -/
theorem selected_even_entry_to6_exact (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right xs : List Nat) (head : Int) (k : Nat)
    (hz : ∀ p≤z, back p=false) (he : value%2=0) (hl : xs.length=14)
    (hbound : head≤ctrl-2) (hstop : back (head+1)=false)
    (hones : ∀ q, head+1<q → q<ctrl → back q=true)
    (hcarry : downHolds back head (List.replicate k true ++ [false]))
    (hwin : Holds back (head-(k : Int)-((encode xs).length : Int)) (markerWindow xs))
    (hleft : back (head-(k : Int)-((encode xs).length : Int)-1)=true) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    let p := head-(k : Int)
    let out := selectorOutputTape back ctrl value left right head k
    ∃ n : Nat, 0<n ∧ out p=true ∧ (∀ q<p, out q=back q) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right))
        (cfg 6 (p-((encode xs).length : Int)+1) out) n := by
  dsimp only
  obtain ⟨n,hn,hm,hprefix,hseg⟩ :=
    selected_even_entry_to93_exact back ctrl z value left right xs head k
      hz he hl hbound hstop hones hcarry hwin hleft
  refine ⟨n+1,by omega,hm,hprefix,?_⟩
  exact selected_window_to6 back _ _ xs _ n hl hwin hprefix hseg

/-! The same assumptions force one more silent transition to state 7. -/
theorem selected_odd_entry_to7_exact (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right xs : List Nat) (k : Nat)
    (hz : ∀ p≤z, back p=false) (ho : value%2=1) (hl : xs.length=14)
    (hcarry : downHolds back (ctrl-1) (List.replicate k true ++ [false]))
    (hwin : Holds back (ctrl-1-(k : Int)-((encode xs).length : Int)) (markerWindow xs))
    (hleft : back (ctrl-1-(k : Int)-((encode xs).length : Int)-1)=true) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    let p := ctrl-1-(k : Int)
    let out := selectorOutputTape back ctrl value left right (ctrl-1) k
    ∃ n : Nat, 0<n ∧ out p=true ∧ (∀ q<p, out q=back q) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right))
        (cfg 7 (p-((encode xs).length : Int)+2) out) n := by
  dsimp only
  obtain ⟨n,hn,hm,hprefix,hseg⟩ :=
    selected_odd_entry_to93_exact back ctrl z value left right xs k hz ho hl hcarry hwin hleft
  refine ⟨n+2,by omega,hm,hprefix,?_⟩
  exact selected_window_to7 back _ _ xs _ n hl hwin hprefix hseg

/-- Even selected value: the same exact state-7 boundary, with the explicit
finite control run required by the even branch. -/
theorem selected_even_entry_to7_exact (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right xs : List Nat) (head : Int) (k : Nat)
    (hz : ∀ p≤z, back p=false) (he : value%2=0) (hl : xs.length=14)
    (hbound : head≤ctrl-2) (hstop : back (head+1)=false)
    (hones : ∀ q, head+1<q → q<ctrl → back q=true)
    (hcarry : downHolds back head (List.replicate k true ++ [false]))
    (hwin : Holds back (head-(k : Int)-((encode xs).length : Int)) (markerWindow xs))
    (hleft : back (head-(k : Int)-((encode xs).length : Int)-1)=true) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    let p := head-(k : Int)
    let out := selectorOutputTape back ctrl value left right head k
    ∃ n : Nat, 0<n ∧ out p=true ∧ (∀ q<p, out q=back q) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right))
        (cfg 7 (p-((encode xs).length : Int)+2) out) n := by
  dsimp only
  obtain ⟨n,hn,hm,hprefix,hseg⟩ :=
    selected_even_entry_to93_exact back ctrl z value left right xs head k
      hz he hl hbound hstop hones hcarry hwin hleft
  refine ⟨n+2,by omega,hm,hprefix,?_⟩
  exact selected_window_to7 back _ _ xs _ n hl hwin hprefix hseg

#print axioms selected_odd_entry_to7_exact
#print axioms selected_even_entry_to7_exact
#print axioms selected_odd_entry_to6_exact
#print axioms selected_even_entry_to6_exact
#print axioms selected_window_to7
#print axioms marker_window_prefix
#print axioms selected_window_to6
#print axioms marker_window_first_zero
#print axioms marker_window_step93

end Shared.Beeping.NPcoNP.NativeHalfWindowDispatch
