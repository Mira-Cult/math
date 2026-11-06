import Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
import Shared.Beeping.NPcoNP.NativeHalfState16Progress
/-! Continue the unit dispatch through the next complete unary block. The
extra trailing block keeps its delimiter separate from the carry marker. -/
namespace Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

theorem holds_prefix_word (t : Int → Bool) (a : Int) (xs ys : List Bool)
    (h : Holds t a (xs++ys)) : Holds t a xs := by
  induction xs generalizing a with
  | nil => trivial
  | cons b xs ih =>
    simp only [List.cons_append,Holds] at h ⊢
    exact ⟨h.1, ih (a+1) h.2⟩

theorem marker_two_blocks (k v y z : Nat) (zs : List Nat) :
    ∃ tail, markerWindow (List.replicate k 0 ++ v :: y :: z :: zs) =
      false :: (encode (List.replicate k 0) ++ block v ++ block y ++ tail) := by
  obtain ⟨tail, ht⟩ := encode_ends_zero (z::zs) (by simp)
  refine ⟨tail, ?_⟩
  apply List.append_cancel_right (bs := [false])
  have hm := markerWindow_append_zero (List.replicate k 0 ++ v :: y :: z :: zs)
  rw [encode_append] at hm
  change markerWindow (List.replicate k 0 ++ v :: y :: z :: zs) ++ [false] =
    false :: (encode (List.replicate k 0) ++ (block v ++ (block y ++ encode (z::zs)))) at hm
  rw [ht] at hm
  simpa [List.append_assoc] using hm

theorem one_marker_tail (t : Int → Bool) (a : Int) (k y z : Nat) (zs : List Nat)
    (hw : Holds t a (markerWindow (List.replicate k 0 ++ 1 :: y :: z :: zs))) :
    let d := a+((2*k : Nat) : Int)+4
    t d=true ∧ Holds t (d+1) (List.replicate y true ++ [false]) := by
  obtain ⟨tail,he⟩ := marker_two_blocks k 1 y z zs
  rw [he] at hw
  have hh := holds_append_tail t (a+1) (encode (List.replicate k 0) ++ block 1)
    (block y ++ tail) (by simpa [List.append_assoc] using hw.2)
  have hl : (encode (List.replicate k 0) ++ block 1).length = 2*k+3 := by
    simp [zeros_length,block_length]
  rw [hl] at hh
  simp only [block,List.replicate_succ,List.cons_append,Holds] at hh
  dsimp only
  have hp : a+1+((2*k+3 : Nat) : Int) = a+((2*k : Nat) : Int)+4 := by push_cast; omega
  rw [hp] at hh
  exact ⟨hh.1, holds_prefix_word t _ _ tail hh.2⟩

theorem marker_unit_to12 (t : Int → Bool) (a : Int) (k y z : Nat) (zs : List Nat)
    (hw : Holds t a (markerWindow (List.replicate k 0 ++ 1 :: y :: z :: zs))) :
    let d := a+((2*k : Nat) : Int)+4
    silentSegment machine (cfg 93 a t) (cfg 12 (d+((y : Nat) : Int)+2) (clearAt d t)) (2*k+y+6) := by
  dsimp only
  have hfirst := marker_window_to_one t a k (y::z::zs) (by simp) hw
  have ht := one_marker_tail t a k y z zs hw
  have h261 := oneSeg machine _ _ (step261_one _ t ht.1)
  have hscan : Holds (clearAt (a+((2*k : Nat) : Int)+4) t)
      (a+((2*k : Nat) : Int)+4+1) (List.replicate y true ++ [false]) := by
    apply holds_clear_left
    · omega
    · exact ht.2
  have h16 := scan16 y _ _ hscan
  have hjoined := segAdd machine _ _ _ 1 (y+1) h261 h16
  have hall := segAdd machine _ _ _ (2*k+4) (1+(y+1)) hfirst hjoined
  have hp : a+((2*k : Nat) : Int)+4+1+(y : Int)+1 = a+((2*k : Nat) : Int)+4+(y : Int)+2 := by omega
  have hn : 2*k+4+(1+(y+1)) = 2*k+y+6 := by omega
  simpa only [hp,hn] using hall

/-- With no later block, the needed delimiter lies on the carry marker.
If that marker is one, the proposed state-16 word cannot be present. -/
theorem single_suffix_carry_incompatible (t : Int → Bool) (a : Int) (k y : Nat)
    (hm : t (a+((encode (List.replicate k 0 ++ [1,y])).length : Int))=true) :
    ¬ Holds t (a+((2*k : Nat) : Int)+5) (List.replicate y true ++ [false]) := by
  intro hw
  have hzero := holds_get t (a+((2*k : Nat) : Int)+5)
    (List.replicate y true ++ [false]) hw y (by simp)
  have hz : t (a+((2*k : Nat) : Int)+5+(y : Int))=false := by simpa using hzero
  have hlen : (encode (List.replicate k 0 ++ [1,y])).length=2*k+y+5 := by
    rw [encode_append]
    simp [zeros_length,encode,block_length]
    omega
  rw [hlen] at hm
  have hp : a+((2*k : Nat) : Int)+5+(y : Int) = a+((2*k+y+5 : Nat) : Int) := by push_cast; omega
  rw [hp] at hz
  rw [hm] at hz
  contradiction

/-- Compose an earlier selected-entry segment with the exact continuation.
The input window may be on the original protected tape prefix. -/
theorem selected_unit_to12 (back out : Int → Bool) (p : Int) (k y z : Nat)
    (zs : List Nat) (start : Config 284) (n : Nat)
    (hwin : Holds back (p-((encode (List.replicate k 0 ++ 1 :: y :: z :: zs)).length : Int))
      (markerWindow (List.replicate k 0 ++ 1 :: y :: z :: zs)))
    (hprefix : ∀ q<p, out q=back q)
    (hseg : silentSegment machine start
      (cfg 93 (p-((encode (List.replicate k 0 ++ 1 :: y :: z :: zs)).length : Int)) out) n) :
    let a := p-((encode (List.replicate k 0 ++ 1 :: y :: z :: zs)).length : Int)
    let d := a+((2*k : Nat) : Int)+4
    silentSegment machine start (cfg 12 (d+(y : Int)+2) (clearAt d out)) (n+(2*k+y+6)) := by
  dsimp only
  have hw := output_window back out p _ hwin hprefix
  exact segAdd machine _ _ _ n (2*k+y+6) hseg
    (marker_unit_to12 out _ k y z zs hw)

open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfEntryCorrect
open Shared.Beeping.NPcoNP.NativeHalfEntryNonzero
open Shared.Beeping.NPcoNP.UnarySuffixShift

/-- From a supplied selected entry, complete the unit dispatch and following
unary scan, with the exact clear recorded. Reachability is not asserted. -/
theorem selected_entry_unit_to12 (back : Int → Bool) (ctrl z0 : Int)
    (value : Nat) (left right : List Nat) (k y z : Nat) (zs : List Nat)
    (hz : ∀ p≤z0, back p=false)
    (hl : (List.replicate k 0 ++ 1 :: y :: z :: zs).length=14)
    (hwindow : ∀ (head : Int) (j : Nat),
      (value%2=1 → head=ctrl-1) → (value%2=0 → head≤ctrl-2) →
      (value%2=0 → back (head+1)=false) →
      (value%2=0 → ∀ q, head+1<q → q<ctrl → back q=true) →
      downHolds back head (List.replicate j true ++ [false]) →
      let p := head-(j : Int)
      let a := p-((encode (List.replicate k 0 ++ 1 :: y :: z :: zs)).length : Int)
      Holds back a (markerWindow (List.replicate k 0 ++ 1 :: y :: z :: zs)) ∧ back (a-1)=true) :
    let xs := List.replicate k 0 ++ 1 :: y :: z :: zs
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
      let d := p-((encode xs).length : Int)+((2*k : Nat) : Int)+4
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right))
        (cfg 12 (d+(y : Int)+2) (clearAt d out)) n := by
  dsimp only
  obtain ⟨n,p,out,hn,hpost,hmark,hprefix,hseg⟩ :=
    selected_entry_to93_with_window back ctrl z0 value left right _ hz hl hwindow
  obtain ⟨head,j,hp,hodd,heven,hstop,hones,hdown,hbank⟩ := hpost
  have hw := (hwindow head j hodd heven hstop hones hdown).1
  rw [← hp] at hw
  have hnext := selected_unit_to12 back out p k y z zs _ n hw hprefix hseg
  exact ⟨n+(2*k+y+6),p,out,by omega,⟨head,j,hp,hodd,heven,hstop,hones,hdown,hbank⟩,
    hmark,hprefix,hnext⟩

#print axioms selected_entry_unit_to12
#print axioms selected_unit_to12
#print axioms single_suffix_carry_incompatible
#print axioms marker_unit_to12

end Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
