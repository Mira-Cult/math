import Shared.Beeping.NPcoNP.NativeHalfEntryReconstruction
import Shared.Beeping.NPcoNP.NativeHalfEntryAllBanks

/-! Reconstruct the canonical positive HALF entry from a supplied exact
control prefix, selected suffix, reserve and blank right tail. -/
namespace Shared.Beeping.NPcoNP.NativeHalfSelectedReconstruction
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfEntryNonzero
open Shared.Beeping.NPcoNP.NativeHalfEntryCorrect
open Shared.Beeping.NPcoNP.NativeHalfEntryReconstruction
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem before_agrees_below_end (t : Int → Bool) (ctrl : Int) (s : List Bool)
    (z0 : t ctrl=false) (z1 : t (ctrl+1)=false) (word : Holds t (ctrl+2) s) :
    ∀ p, p<ctrl+2+(s.length : Int) → before t ctrl s p=t p := by
  intro p hp
  by_cases hleft : p<ctrl
  · exact before_prefix t ctrl p s hleft
  · by_cases hgap : p<ctrl+2
    · have he : p=ctrl ∨ p=ctrl+1 := by omega
      rcases he with rfl | rfl
      · simp [before,z0]
      · simp [before,z1,show ¬ctrl+1<ctrl by omega]
    · let i := (p-(ctrl+2)).toNat
      have hi : (i : Int)=p-(ctrl+2) := Int.toNat_of_nonneg (by omega)
      have hib : i<s.length := by omega
      have he : ctrl+2+(i : Int)=p := by omega
      have hh := holds_get t (ctrl+2) s word i hib
      rw [he] at hh
      have hi' : (p-ctrl-2).toNat=i := by congr 1 <;> omega
      simp [before,hleft,hgap,hi',bitAt,List.getElem?_eq_getElem hib,hh]

theorem entryTape_congr_left (a b : Int → Bool) (p : Int) (m : Nat) (right : List Nat)
    (same : ∀ q, q<p → a q=b q) : entryTape a p m right=entryTape b p m right := by
  funext q
  by_cases hq : q<p
  · rw [entryTape,entryTape,put_other _ _ _ _ (by omega),put_other _ _ _ _ (by omega),
      prepared_left _ _ _ _ _ hq,prepared_left _ _ _ _ _ hq]
    exact same q hq
  · simp [entryTape,NativeHalfAllResiduals.prepared_shape,put,after,hq]

/-- The canonical two-bank positive selected tape equals a supplied physical
tape when its control prefix, suffix, reserve and blank tail agree exactly. -/
theorem positive_selected_tape_eq (t : Int → Bool) (ctrl z : Int) (left right : List Nat) (m : Nat)
    (z0 : t ctrl=false) (z1 : t (ctrl+1)=false)
    (leftWord : Holds t (ctrl+2) (leftSuffix left))
    (head : t (ctrl+2+((leftSuffix left).length : Int))=true)
    (selected : t (ctrl+2+((leftSuffix left).length : Int)-1)=true)
    (hz : ∀ q, q≤z → t q=false) (hzb : z<ctrl+2+((leftSuffix left).length : Int))
    (word : Holds t (ctrl+2+((leftSuffix left).length : Int)+1)
      ((List.replicate m true ++ false::encode right) ++ [true,false]))
    (tail : ∀ q, ctrl+2+((leftSuffix left).length : Int)+2+
      (((List.replicate m true ++ false::encode right).length : Nat):Int)≤q → t q=false) :
    let base := before t ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    selectedTape base b (m+1) right=t := by
  dsimp only
  let b := ctrl+2+((leftSuffix left).length : Int)
  let base := before t ctrl (leftSuffix left)
  obtain ⟨he,_,_⟩ := entryTape_eq_of_word t b z m right head selected hz hzb word tail
  have same : ∀ p, p<b → base p=clearAt b t p := by
    intro p hp
    have hb := before_agrees_below_end t ctrl (leftSuffix left) z0 z1 leftWord p hp
    simpa [base,clearAt,show p≠b by omega] using hb
  have hh := entryTape_congr_left base (clearAt b t) b m right same
  change entryTape base b m right=t
  exact hh.trans he

/-- The literal positive HALF operation on a physical word preserves both
banks, emits no event, produces the quotient and retains a final reserve,
under the stated exact-prefix and blank-tail hypotheses. -/
theorem positive_selected_of_word (t : Int → Bool) (ctrl z : Int) (left right : List Nat) (m : Nat)
    (z0 : t ctrl=false) (z1 : t (ctrl+1)=false)
    (leftWord : Holds t (ctrl+2) (leftSuffix left))
    (head : t (ctrl+2+((leftSuffix left).length : Int))=true)
    (selected : t (ctrl+2+((leftSuffix left).length : Int)-1)=true)
    (hz : ∀ q, q≤z → t q=false) (hzb : z<ctrl+2+((leftSuffix left).length : Int))
    (word : Holds t (ctrl+2+((leftSuffix left).length : Int)+1)
      ((List.replicate m true ++ false::encode right) ++ [true,false]))
    (tail : ∀ q, ctrl+2+((leftSuffix left).length : Int)+2+
      (((List.replicate m true ++ false::encode right).length : Nat):Int)≤q → t q=false) :
    let b := ctrl+2+((leftSuffix left).length : Int)
    let values := left ++ [(m+1)/2] ++ right ++ List.replicate ((m+2)/2) 0
    ∃ (steps : Nat) (headPos : Int) (out : Int → Bool), 0<steps ∧
      ((m+1)%2=1 → headPos=ctrl-1) ∧
      ((m+1)%2=0 → headPos≤ctrl-2) ∧
      ((m+1)%2=0 → t (headPos+1)=false) ∧
      ((m+1)%2=0 → ∀ p, headPos+1<p → p<ctrl → t p=true) ∧
      ((m+1)%2=0 → ∀ p, headPos+2≤p → p<ctrl → out p=false) ∧
      ((m+1)%2=1 → ∀ p<ctrl, out p=t p) ∧
      ((m+1)%2=0 → ∀ p≤headPos+1, out p=t p) ∧
      out (headPos+1)=false ∧ out ctrl=false ∧ out (ctrl+1)=false ∧
      Holds out (ctrl+2) (encode values) ∧
      out (ctrl+2+((encode values).length : Int))=true ∧
      out (ctrl+3+((encode values).length : Int))=false ∧
      (∀ p, ctrl+3+((encode values).length : Int)≤p → out p=false) ∧
      silentSegment machine (cfg 29 (b-1) t) (cfg 1 headPos out) steps := by
  dsimp only
  have he := positive_selected_tape_eq t ctrl z left right m z0 z1 leftWord head selected hz hzb word tail
  obtain ⟨steps,headPos,out,hs,hodd,heven,hstop,hones,hclear,hoddframe,hevenframe,hz,hctrl,hctrl1,hbank,hmark,hblank,htail,hsegment⟩ :=
    Shared.Beeping.NPcoNP.NativeHalfEntryAllBanks.selected_entry_packed_bank t ctrl z (m+1) left right hz
  rw [he] at hsegment
  exact ⟨steps,headPos,out,hs,hodd,heven,hstop,hones,hclear,hoddframe,hevenframe,hz,hctrl,hctrl1,
    by simpa [Nat.add_assoc] using hbank,by simpa [Nat.add_assoc] using hmark,
    by simpa [Nat.add_assoc] using hblank,by simpa [Nat.add_assoc] using htail,hsegment⟩

#print axioms positive_selected_tape_eq
#print axioms positive_selected_of_word
end Shared.Beeping.NPcoNP.NativeHalfSelectedReconstruction
