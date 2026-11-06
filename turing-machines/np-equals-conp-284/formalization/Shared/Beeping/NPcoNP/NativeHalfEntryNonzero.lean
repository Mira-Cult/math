import Shared.Beeping.NPcoNP.NativeHalfPreparedCorrect
import Shared.Beeping.NPcoNP.NativeHalfScannerFrames
import Shared.Beeping.NPcoNP.NativeHalfCyclePrelude
import Shared.Beeping.NPcoNP.NativeHalfCleanupScan

/-! Literal native-HALF entry for nonzero values, connected to the proved
prepared-loop contract. Selector reachability and return-branch meaning
remain separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeHalfEntryNonzero

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfCyclePrelude
open Shared.Beeping.NPcoNP.NativeHalfCleanupScan
open Shared.Beeping.NPcoNP.NativeHalfAllResiduals
open Shared.Beeping.NPcoNP.NativeHalfPreparedCorrect
open Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

theorem row29_one : machine.table.row 29 true=⟨true,.right,41,false⟩ := by decide
theorem row41_one : machine.table.row 41 true=⟨true,.right,40,false⟩ := by decide

theorem step29_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 29 h t)=(cfg 41 (h+1) t,false) := by
  have hw : (⟨29,h,t⟩ : Config 284).write true=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row29_one,Move.apply,hw]

theorem step41_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 41 h t)=(cfg 40 (h+1) t,false) := by
  have hw : (⟨41,h,t⟩ : Config 284).write true=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row41_one,Move.apply,hw]

/-- Remove a proved silent one-step prefix from a longer silent segment. -/
theorem silent_tail_one (c d e : Config 284) (n : Nat)
    (hfirst : silentSegment machine c d 1)
    (h : silentSegment machine c e (1+n)) :
    silentSegment machine d e n := by
  constructor
  · have hh := h.1
    rw [WordEventSystem.advance_add,hfirst.1] at hh
    exact hh
  · have hw := h.2
    rw [WordEventSystem.wordFrom_add,hfirst.1,hfirst.2] at hw
    simpa using hw

def entryTape (base : Int → Bool) (b : Int) (m : Nat) (xs : List Nat) : Int → Bool :=
  put (prepared base b m xs) b true

theorem prepared_boundary (base : Int → Bool) (b : Int) (m : Nat) (xs : List Nat) :
    prepared base b m xs b=false := by
  rw [prepared_shape]
  exact (gap_cells base b (List.replicate m true ++ false :: encode xs)).2.2

theorem prepared_left (base : Int → Bool) (b p : Int) (m : Nat) (xs : List Nat) (hp : p<b) :
    prepared base b m xs p=base p := by
  rw [prepared_shape]
  exact after_prefix base b p _ hp

/-- At the literal entry, the selected block is exactly `m+2` ones and a
zero, followed by the encoded suffix and the paid reserve. -/
theorem entry_layout (base : Int → Bool) (b : Int) (m : Nat) (xs : List Nat)
    (hb : base (b-1)=true) :
    Holds (entryTape base b m xs) (b-1)
      (block (m+1) ++ encode xs ++ [true,false,false]) := by
  let s := List.replicate m true ++ false :: encode xs
  have hp : prepared base b m xs=after base b s := prepared_shape base b m xs
  have hh := holds_after_suffix base b s
  have hframe : Holds (entryTape base b m xs) (b+1) (s ++ [true,false,false]) := by
    apply holds_transport (prepared base b m xs) _ (b+1) _ (by rw [hp]; exact hh)
    intro p hlo hhi
    change prepared base b m xs p=put (prepared base b m xs) b true p
    rw [put_other _ _ _ _ (by omega)]
  have hleft : entryTape base b m xs (b-1)=true := by
    unfold entryTape
    rw [put_other _ _ _ _ (by omega),prepared_left _ _ _ _ _ (by omega)]
    exact hb
  have hmiddle : entryTape base b m xs b=true := by simp [entryTape,put]
  have hwords : Holds (entryTape base b m xs) (b-1)
      (true :: true :: (s ++ [true,false,false])) := by
    change entryTape base b m xs (b-1)=true ∧
      Holds (entryTape base b m xs) ((b-1)+1) (true :: (s ++ [true,false,false]))
    refine ⟨hleft,?_⟩
    have he : (b-1)+1=b := by omega
    rw [he]
    exact ⟨hmiddle,hframe⟩
  simpa [s,block,List.replicate_succ,Nat.add_assoc,List.append_assoc] using hwords

/-- The two paid entry transitions arrive at exactly the successor of the
first prepared-loop transition. -/
theorem entry_to_prepared_successor (base : Int → Bool) (b : Int) (m : Nat)
    (xs : List Nat) (hb : base (b-1)=true) :
    silentSegment machine (cfg 29 (b-1) (entryTape base b m xs))
      (cfg 40 (b+1) (entryTape base b m xs)) 2 ∧
    silentSegment machine (cfg 30 b (prepared base b m xs))
      (cfg 40 (b+1) (entryTape base b m xs)) 1 := by
  have hleft : entryTape base b m xs (b-1)=true := by
    unfold entryTape
    rw [put_other _ _ _ _ (by omega),prepared_left _ _ _ _ _ (by omega)]
    exact hb
  have hmiddle : entryTape base b m xs b=true := by simp [entryTape,put]
  have ha := oneSeg machine _ _ (step29_one (b-1) (entryTape base b m xs) hleft)
  have hb' := oneSeg machine _ _ (step41_one b (entryTape base b m xs) hmiddle)
  have ha' : silentSegment machine (cfg 29 (b-1) (entryTape base b m xs))
      (cfg 41 b (entryTape base b m xs)) 1 := by
    simpa only [Int.sub_add_cancel] using ha
  have hentry := segAdd machine _ _ _ 1 1 ha' hb'
  have hprep := oneSeg machine _ _ (step30 b (prepared base b m xs) (prepared_boundary base b m xs))
  constructor
  · simpa only [Int.sub_add_cancel] using hentry
  · exact hprep

/-- For a nonzero selected value `m+1`, the literal entry completes a
positive silent segment to state 1 with the quotient and suffix contract.
The entry layout and later return-control meaning are explicit interfaces. -/
theorem entry_nonzero_quotient_and_bank (base : Int → Bool) (b z : Int) (m : Nat)
    (xs : List Nat) (hb : base (b-1)=true) (hz : ∀ p≤z, base p=false) :
    ∃ (n : Nat) (head gap : Int) (finalTape : Int → Bool), 0<n ∧
      Holds finalTape (b-1) (block ((m+1)/2)) ∧
      let values := xs ++ List.replicate (m/2+1) 0
      let word := encode values
      decode (xs.length+(m/2+1)) (readCells finalTape (gap+2) word.length)=some (values,[]) ∧
      finalTape (gap+2+(word.length : Int))=true ∧
      finalTape (gap+3+(word.length : Int))=false ∧
      silentSegment machine (cfg 29 (b-1) (entryTape base b m xs))
        (cfg 1 head finalTape) n := by
  have hleft : ∀ p, b-(1 : Int)≤p → p<b → base p=true := by
    intro p hp hp'
    have he : p=b-1 := by omega
    rw [he]
    exact hb
  obtain ⟨n₁,n₂,head,gap,t,hn₁,hn₂,_,hquot,hdec,hr0,hr1,hseg⟩ :=
    prepared_quotient_and_bank base b z 1 m xs (by decide) hz hleft
  have hval : sourceValue 1 m=m+1 := by simp [sourceValue]
  have hquot' : Holds t (b-1) (block ((m+1)/2)) := by simpa only [hval,Nat.cast_one] using hquot
  obtain ⟨hentry,hprep⟩ := entry_to_prepared_successor base b m xs hb
  let rest := n₁+n₂-1
  have hlen : 1+rest=n₁+n₂ := by dsimp [rest]; omega
  rw [← hlen] at hseg
  have htail := silent_tail_one _ _ _ rest hprep hseg
  exact ⟨2+rest,head,gap,t,by omega,hquot',hdec,hr0,hr1,
    segAdd machine _ _ _ 2 rest hentry htail⟩

end Shared.Beeping.NPcoNP.NativeHalfEntryNonzero

#print axioms Shared.Beeping.NPcoNP.NativeHalfEntryNonzero.entry_layout
#print axioms Shared.Beeping.NPcoNP.NativeHalfEntryNonzero.entry_nonzero_quotient_and_bank
