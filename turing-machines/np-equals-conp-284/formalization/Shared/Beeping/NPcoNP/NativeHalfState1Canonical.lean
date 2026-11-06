import Shared.Beeping.NPcoNP.NativeHalfEntryAllBanks
import Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

/-! Whole-tape state-1 layout after the selected native-HALF entry. -/
namespace Shared.Beeping.NPcoNP.NativeHalfState1Canonical

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfEntryCorrect
open Shared.Beeping.NPcoNP.NativeHalfEntryAllBanks
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

/-- The state-95 branch clears the original control prefix strictly above
`head+1`; on the odd branch this interval is empty. The bank and final `10`
are explicitly represented, with a blank right tail. -/
def state1Tape (back : Int → Bool) (ctrl head : Int) (values : List Nat) : Int → Bool :=
  before (fun p => if head+1<p then false else back p) ctrl (encode values ++ [true,false])

/-- The local cell and tail facts uniquely determine the entire two-way tape. -/
theorem tape_eq_state1Tape (back : Int → Bool) (ctrl head : Int) (values : List Nat)
    (t : Int → Bool)
    (hleft : ∀ p<ctrl, t p=(if head+1<p then false else back p))
    (h0 : t ctrl=false) (h1 : t (ctrl+1)=false)
    (hbank : Holds t (ctrl+2) (encode values))
    (hr0 : t (ctrl+2+((encode values).length : Int))=true)
    (hr1 : t (ctrl+3+((encode values).length : Int))=false)
    (htail : ∀ p, ctrl+3+((encode values).length : Int)≤p → t p=false) :
    t=state1Tape back ctrl head values := by
  let word := encode values ++ [true,false]
  have hpair : Holds t (ctrl+2+((encode values).length : Int)) [true,false] := by
    change t (ctrl+2+((encode values).length : Int))=true ∧
      t (ctrl+2+((encode values).length : Int)+1)=false ∧ True
    refine ⟨hr0,?_,trivial⟩
    have he : ctrl+2+((encode values).length : Int)+1=ctrl+3+((encode values).length : Int) := by omega
    rwa [he]
  have hword : Holds t (ctrl+2) word :=
    holds_append t (ctrl+2) (encode values) [true,false] hbank hpair
  funext p
  change t p=before (fun q => if head+1<q then false else back q) ctrl word p
  by_cases hp0 : p<ctrl
  · rw [before_prefix _ _ _ _ hp0]
    exact hleft p hp0
  · by_cases hp1 : p<ctrl+2
    · have hp : p=ctrl ∨ p=ctrl+1 := by omega
      rcases hp with rfl | rfl
      · simpa [before] using h0
      · simpa [before] using h1
    · by_cases hp2 : p<ctrl+2+((word.length : Nat) : Int)
      · let i := (p-ctrl-2).toNat
        have hiint : (i : Int)=p-ctrl-2 := Int.toNat_of_nonneg (by omega)
        have hi : i<word.length := by omega
        have he : p=ctrl+2+(i : Int) := by omega
        rw [he,before_suffix_bit]
        have hh := holds_get t (ctrl+2) word hword i hi
        simpa [bitAt,List.getElem?_eq_getElem hi] using hh
      · have htail' : ctrl+3+((encode values).length : Int)≤p := by
          dsimp [word] at hp2
          simp only [List.length_append,List.length_cons,List.length_nil,Nat.cast_add,Nat.cast_ofNat] at hp2
          omega
        rw [htail p htail']
        symm
        apply before_tail_zero
        omega

/-- The odd and even return conditions determine the control prefix of the
canonical tape, while the bank facts determine the rest. -/
theorem tape_eq_state1Tape_of_parity (back : Int → Bool) (ctrl head : Int)
    (value : Nat) (values : List Nat) (t : Int → Bool)
    (hodd : value%2=1 → head=ctrl-1)
    (hclear : value%2=0 → ∀ p, head+2≤p → p<ctrl → t p=false)
    (hoddback : value%2=1 → ∀ p<ctrl, t p=back p)
    (hevenback : value%2=0 → ∀ p≤head+1, t p=back p)
    (h0 : t ctrl=false) (h1 : t (ctrl+1)=false)
    (hbank : Holds t (ctrl+2) (encode values))
    (hr0 : t (ctrl+2+((encode values).length : Int))=true)
    (hr1 : t (ctrl+3+((encode values).length : Int))=false)
    (htail : ∀ p, ctrl+3+((encode values).length : Int)≤p → t p=false) :
    t=state1Tape back ctrl head values := by
  have hleft : ∀ p<ctrl, t p=(if head+1<p then false else back p) := by
    intro p hp
    by_cases hv : value%2=0
    · by_cases hc : head+1<p
      · rw [if_pos hc]
        exact hclear hv p (by omega) hp
      · rw [if_neg hc]
        exact hevenback hv p (by omega)
    · have hv' : value%2=1 := by omega
      have hh := hodd hv'
      have hc : ¬ head+1<p := by omega
      rw [if_neg hc]
      exact hoddback hv' p hp
  exact tape_eq_state1Tape back ctrl head values t hleft h0 h1 hbank hr0 hr1 htail

/-- From a supplied selected entry the exact state-1 tape is computable from
the original prefix, returned head and updated finite register bank. -/
theorem selected_entry_packed_exact (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right : List Nat) (hz : ∀ p≤z, back p=false) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    let values := left ++ [value/2] ++ right ++ List.replicate ((value+1)/2) 0
    ∃ (steps : Nat) (head : Int), 0<steps ∧
      (value%2=1 → head=ctrl-1) ∧
      (value%2=0 → head≤ctrl-2) ∧
      (value%2=0 → back (head+1)=false) ∧
      (value%2=0 → ∀ p, head+1<p → p<ctrl → back p=true) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right))
        (cfg 1 head (state1Tape back ctrl head values)) steps := by
  dsimp only
  obtain ⟨n,head,t,hn,hodd,heven,hstopBack,honesBack,hclear,hoddback,hevenback,
    hstop,hctrl,hctrl1,hbank,hr0,hr1,htail,hseg⟩ :=
      selected_entry_packed_bank back ctrl z value left right hz
  have ht := tape_eq_state1Tape_of_parity back ctrl head value _ t hodd hclear
    hoddback hevenback hctrl hctrl1 hbank hr0 hr1 htail
  refine ⟨n,head,hn,hodd,heven,hstopBack,honesBack,?_⟩
  rw [← ht]
  exact hseg

end Shared.Beeping.NPcoNP.NativeHalfState1Canonical

#print axioms Shared.Beeping.NPcoNP.NativeHalfState1Canonical.selected_entry_packed_exact
