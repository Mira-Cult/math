import Shared.Beeping.NPcoNP.NativeHalfWindowZeroScan
/-! Connect the selected-entry marker window to its exact dispatch scan.
The tape-layout hypotheses remain explicit; no graph reachability is claimed. -/
namespace Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfWindowDispatch
open Shared.Beeping.NPcoNP.NativeHalfWindowZeroScan
open Shared.Beeping.NPcoNP.UnaryBank
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

theorem encode_ends_zero (xs : List Nat) (hne : xs ≠ []) : ∃ front, encode xs = front ++ [false] := by
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
    cases ys with
    | nil => exact ⟨List.replicate (y+1) true, by simp [encode,block]⟩
    | cons z zs =>
      obtain ⟨front, hf⟩ := ih (by simp)
      refine ⟨block y ++ front, ?_⟩
      change block y ++ encode (z::zs) = (block y ++ front) ++ [false]
      rw [hf,List.append_assoc]

theorem marker_window_prefix_block (k v : Nat) (rest : List Nat) (hne : rest ≠ []) :
    ∃ tail, markerWindow (List.replicate k 0 ++ v :: rest) =
      false :: (encode (List.replicate k 0) ++ block v ++ tail) := by
  have hend := encode_ends_zero rest hne
  obtain ⟨tail,htail⟩ := hend
  refine ⟨tail, ?_⟩
  apply List.append_cancel_right (bs := [false])
  have hm := markerWindow_append_zero (List.replicate k 0 ++ v :: rest)
  rw [encode_append] at hm
  change markerWindow (List.replicate k 0 ++ v :: rest) ++ [false] =
    false :: (encode (List.replicate k 0) ++ (block v ++ encode rest)) at hm
  rw [htail] at hm
  simpa [List.append_assoc] using hm

/-- From the exact state-93 marker window, scan k zero-valued blocks and a
unit block, reaching state 261 in exactly 2*k+4 silent steps. -/
theorem marker_window_to_one (t : Int → Bool) (a : Int) (k : Nat)
    (rest : List Nat) (hne : rest ≠ [])
    (hw : Holds t a (markerWindow (List.replicate k 0 ++ 1 :: rest))) :
    silentSegment machine (cfg 93 a t) (cfg 261 (a+((2*k : Nat) : Int)+4) t) (2*k+4) := by
  obtain ⟨tail, he⟩ := marker_window_prefix_block k 1 rest hne
  rw [he] at hw
  have hfirst := oneSeg machine _ _ (Shared.Beeping.NPcoNP.NativeHalfState93Progress.step93_zero a t hw.1)
  have hscan := zero_blocks_then_one t (a+1) k tail hw.2
  have h := segAdd machine _ _ _ 1 (2*k+3) hfirst hscan
  have hp : (a+1)+((2*k : Nat) : Int)+3 = a+((2*k : Nat) : Int)+4 := by omega
  have hn : 1+(2*k+3)=2*k+4 := by omega
  simpa only [hp,hn] using h

/-- A next block of value at least two instead reaches state 260 with the
same exact duration and unchanged tape. -/
theorem marker_window_to_ge_two (t : Int → Bool) (a : Int) (k x : Nat)
    (rest : List Nat) (hne : rest ≠ [])
    (hw : Holds t a (markerWindow (List.replicate k 0 ++ (x+2) :: rest))) :
    silentSegment machine (cfg 93 a t) (cfg 260 (a+((2*k : Nat) : Int)+4) t) (2*k+4) := by
  obtain ⟨tail, he⟩ := marker_window_prefix_block k (x+2) rest hne
  rw [he] at hw
  have hfirst := oneSeg machine _ _ (Shared.Beeping.NPcoNP.NativeHalfState93Progress.step93_zero a t hw.1)
  have hscan := zero_blocks_then_ge_two t (a+1) k x tail hw.2
  have h := segAdd machine _ _ _ 1 (2*k+3) hfirst hscan
  have hp : (a+1)+((2*k : Nat) : Int)+3 = a+((2*k : Nat) : Int)+4 := by omega
  have hn : 1+(2*k+3)=2*k+4 := by omega
  simpa only [hp,hn] using h

#print axioms marker_window_to_one
#print axioms marker_window_to_ge_two

open Shared.Beeping.NPcoNP.NativeHalfScannerFrames

theorem output_window (back out : Int → Bool) (p : Int) (xs : List Nat)
    (hwin : Holds back (p-((encode xs).length : Int)) (markerWindow xs))
    (hprefix : ∀ q<p, out q=back q) :
    Holds out (p-((encode xs).length : Int)) (markerWindow xs) := by
  apply holds_transport back out _ _ hwin
  intro q hlo hhi
  symm
  apply hprefix
  rw [markerWindow_length] at hhi
  omega

theorem selected_to_one (back out : Int → Bool) (p : Int) (k : Nat)
    (rest : List Nat) (start : Config 284) (n : Nat) (hne : rest ≠ [])
    (hwin : Holds back (p-((encode (List.replicate k 0 ++ 1 :: rest)).length : Int))
      (markerWindow (List.replicate k 0 ++ 1 :: rest)))
    (hprefix : ∀ q<p, out q=back q)
    (hseg : silentSegment machine start
      (cfg 93 (p-((encode (List.replicate k 0 ++ 1 :: rest)).length : Int)) out) n) :
    silentSegment machine start
      (cfg 261 (p-((encode (List.replicate k 0 ++ 1 :: rest)).length : Int)+
        ((2*k : Nat) : Int)+4) out) (n+(2*k+4)) := by
  have hw := output_window back out p _ hwin hprefix
  exact segAdd machine _ _ _ n (2*k+4) hseg
    (marker_window_to_one out _ k rest hne hw)

theorem selected_to_ge_two (back out : Int → Bool) (p : Int) (k x : Nat)
    (rest : List Nat) (start : Config 284) (n : Nat) (hne : rest ≠ [])
    (hwin : Holds back (p-((encode (List.replicate k 0 ++ (x+2) :: rest)).length : Int))
      (markerWindow (List.replicate k 0 ++ (x+2) :: rest)))
    (hprefix : ∀ q<p, out q=back q)
    (hseg : silentSegment machine start
      (cfg 93 (p-((encode (List.replicate k 0 ++ (x+2) :: rest)).length : Int)) out) n) :
    silentSegment machine start
      (cfg 260 (p-((encode (List.replicate k 0 ++ (x+2) :: rest)).length : Int)+
        ((2*k : Nat) : Int)+4) out) (n+(2*k+4)) := by
  have hw := output_window back out p _ hwin hprefix
  exact segAdd machine _ _ _ n (2*k+4) hseg
    (marker_window_to_ge_two out _ k x rest hne hw)

#print axioms selected_to_one
#print axioms selected_to_ge_two

theorem selected_dispatch (back out : Int → Bool) (p : Int) (k v : Nat)
    (rest : List Nat) (start : Config 284) (n : Nat) (hv : 0<v) (hne : rest ≠ [])
    (hwin : Holds back (p-((encode (List.replicate k 0 ++ v :: rest)).length : Int))
      (markerWindow (List.replicate k 0 ++ v :: rest)))
    (hprefix : ∀ q<p, out q=back q)
    (hseg : silentSegment machine start
      (cfg 93 (p-((encode (List.replicate k 0 ++ v :: rest)).length : Int)) out) n) :
    silentSegment machine start
      (cfg (if v=1 then 261 else 260)
        (p-((encode (List.replicate k 0 ++ v :: rest)).length : Int)+
        ((2*k : Nat) : Int)+4) out) (n+(2*k+4)) := by
  cases v with
  | zero => omega
  | succ v =>
    cases v with
    | zero => simpa using selected_to_one back out p k rest start n hne hwin hprefix hseg
    | succ x =>
      simpa [Nat.succ_eq_add_one] using selected_to_ge_two back out p k x rest start n hne hwin hprefix hseg

open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfEntryCorrect
open Shared.Beeping.NPcoNP.NativeHalfEntryNonzero
open Shared.Beeping.NPcoNP.UnarySuffixShift

theorem selected_entry_to_dispatch (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right : List Nat) (k v : Nat) (rest : List Nat)
    (hv : 0<v) (hne : rest ≠ [])
    (hz : ∀ p≤z, back p=false)
    (hl : (List.replicate k 0 ++ v :: rest).length=14)
    (hwindow : ∀ (head : Int) (j : Nat),
      (value%2=1 → head=ctrl-1) → (value%2=0 → head≤ctrl-2) →
      (value%2=0 → back (head+1)=false) →
      (value%2=0 → ∀ q, head+1<q → q<ctrl → back q=true) →
      downHolds back head (List.replicate j true ++ [false]) →
      let p := head-(j : Int)
      let a := p-((encode (List.replicate k 0 ++ v :: rest)).length : Int)
      Holds back a (markerWindow (List.replicate k 0 ++ v :: rest)) ∧ back (a-1)=true) :
    let xs := List.replicate k 0 ++ v :: rest
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    ∃ (n : Nat) (p : Int) (out : Int → Bool), 0<n ∧
      (∃ (head : Int) (j : Nat), p=head-(j : Int) ∧
        (value%2=1 → head=ctrl-1) ∧ (value%2=0 → head≤ctrl-2) ∧
        (value%2=0 → back (head+1)=false) ∧
        (value%2=0 → ∀ q, head+1<q → q<ctrl → back q=true) ∧
        downHolds back head (List.replicate j true ++ [false]) ∧
        BankPost back ctrl value left right head j out) ∧
      out p=true ∧ (∀ q<p, out q=back q) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right))
        (cfg (if v=1 then 261 else 260)
          (p-((encode xs).length : Int)+((2*k : Nat) : Int)+4) out) n := by
  dsimp only
  obtain ⟨n,p,out,hn,hpost,hmark,hprefix,hseg⟩ :=
    selected_entry_to93_with_window back ctrl z value left right _ hz hl hwindow
  obtain ⟨head,j,hp,hodd,heven,hstop,hones,hdown,hbank⟩ := hpost
  have hw := (hwindow head j hodd heven hstop hones hdown).1
  rw [← hp] at hw
  have hnext := selected_dispatch back out p k v rest _ n hv hne hw hprefix hseg
  exact ⟨n+(2*k+4),p,out,by omega,⟨head,j,hp,hodd,heven,hstop,hones,hdown,hbank⟩,
    hmark,hprefix,hnext⟩

#print axioms selected_dispatch
#print axioms selected_entry_to_dispatch

end Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
