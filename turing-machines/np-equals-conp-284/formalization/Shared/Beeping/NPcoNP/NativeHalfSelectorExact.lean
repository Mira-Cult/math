import Shared.Beeping.NPcoNP.NativeHalfSelectorScan
import Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
import Shared.Beeping.NPcoNP.NativeHalfSweep
import Shared.Beeping.NPcoNP.UnaryBank
import Shared.Beeping.NPcoNP.NativeHalfSweepShape

/-! Exact silent selector scans over unary tape blocks. The prepared-bank
theorem gives the physical reverse orientation, head position and duration;
it does not establish reachability or identify graph registers. -/
set_option autoImplicit false

namespace Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

def blocks : List Nat → List Bool
  | [] => []
  | k::ks => List.replicate k true ++ false :: blocks ks

theorem scan_block {q r : Fin 284} (hr : ScanRow q r) (k : Nat) (h : Int)
    (t : Int → Bool) (rest : List Bool)
    (hm : downHolds t h (List.replicate k true ++ false :: rest)) :
    downHolds t (h-((k+1 : Nat) : Int)) rest ∧
      silentSegment machine (cfg q h t) (cfg r (h-((k+1 : Nat) : Int)) t) (k+1) := by
  induction k generalizing h with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, downHolds] at hm
    constructor
    · simpa using hm.2
    · simpa using oneSeg machine _ _ (step_zero hr h t hm.1)
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, downHolds] at hm
    obtain ⟨htail,hseg⟩ := ih (h-1) hm.2
    have hf := oneSeg machine _ _ (step_one hr h t hm.1)
    have hs := segAdd machine _ _ _ 1 (k+1) hf hseg
    have he : (h-1)-((k+1 : Nat) : Int)=h-((Nat.succ k+1 : Nat) : Int) := by push_cast; omega
    rw [he] at htail hs
    constructor
    · exact htail
    · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs

theorem chain_blocks {m : Nat} {q r : Fin 284} (hc : Chain m q r)
    (ks : List Nat) (h : Int) (t : Int → Bool) (rest : List Bool)
    (hl : ks.length=m) (hm : downHolds t h (blocks ks ++ rest)) :
    downHolds t (h-((blocks ks).length : Int)) rest ∧
      silentSegment machine (cfg q h t) (cfg r (h-((blocks ks).length : Int)) t)
        (blocks ks).length := by
  induction hc generalizing ks h with
  | refl q =>
    cases ks with
    | nil =>
      simp only [blocks, List.nil_append, List.length_nil, Nat.cast_zero, sub_zero] at hm ⊢
      refine ⟨hm, ?_⟩
      simp [silentSegment,WordEventSystem.advance,WordEventSystem.wordFrom]
    | cons k ks => simp at hl
  | @cons m q r s hr tail ih =>
    cases ks with
    | nil => simp at hl
    | cons k ks =>
      have hl' : ks.length=m := by simp at hl; omega
      have hm' : downHolds t h (List.replicate k true ++ false :: (blocks ks ++ rest)) := by
        simpa [blocks,List.append_assoc] using hm
      obtain ⟨hrest,hfirst⟩ := scan_block hr k h t (blocks ks ++ rest) hm'
      obtain ⟨hlast,hsecond⟩ := ih ks (h-((k+1 : Nat) : Int)) hl' hrest
      have hs := segAdd machine _ _ _ (k+1) (blocks ks).length hfirst hsecond
      have he : h-((k+1 : Nat) : Int)-((blocks ks).length : Int)=
          h-(((k+1+(blocks ks).length : Nat)) : Int) := by push_cast; omega
      rw [he] at hlast hs
      constructor
      · simpa [blocks,List.length_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hlast
      · simpa [blocks,List.length_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs

end Shared.Beeping.NPcoNP.NativeHalfSelectorExact
#print axioms Shared.Beeping.NPcoNP.NativeHalfSelectorExact.chain_blocks

namespace Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan

theorem blocks_encode (xs : List Nat) : blocks (xs.map (fun n => n+1)) = encode xs := by
  induction xs with
  | nil => rfl
  | cons n ns ih => simp [blocks,encode,block,ih,List.append_assoc]

/-- Fourteen unary values encountered in scan order determine the exact
selector segment, ending at the next tape cell after their last delimiter. -/
theorem selector_on_values (xs : List Nat) (h : Int) (t : Int → Bool) (rest : List Bool)
    (hl : xs.length=14) (hm : downHolds t h (encode xs ++ rest)) :
    downHolds t (h-((encode xs).length : Int)) rest ∧
      silentSegment machine (cfg 83 h t) (cfg 92 (h-((encode xs).length : Int)) t)
        (encode xs).length := by
  have hlen : (xs.map (fun n => n+1)).length=14 := by simpa using hl
  have hm' : downHolds t h (blocks (xs.map (fun n => n+1)) ++ rest) := by
    simpa only [blocks_encode] using hm
  have hr := chain_blocks chain83 (xs.map (fun n => n+1)) h t rest hlen hm'
  simpa only [blocks_encode] using hr

end Shared.Beeping.NPcoNP.NativeHalfSelectorExact
#print axioms Shared.Beeping.NPcoNP.NativeHalfSelectorExact.selector_on_values

namespace Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.UnaryBank

theorem encode_reverse (xs : List Nat) :
    (encode xs).reverse ++ [false] = false :: encode xs.reverse := by
  induction xs with
  | nil => rfl
  | cons n ns ih =>
    simp only [encode,List.reverse_cons,List.reverse_append,block,List.reverse_cons,
      List.reverse_nil,List.nil_append,List.reverse_replicate]
    rw [encode_append]
    simp only [encode,List.append_nil]
    rw [← List.append_assoc, ih]
    simp [block]

end Shared.Beeping.NPcoNP.NativeHalfSelectorExact

namespace Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.UnarySuffixShift

/-- In the actual left-to-right bank representation, starting immediately
left of the final separator scans the values in reverse order. -/
theorem selector_before_encoded (back : Int → Bool) (gap : Int) (xs : List Nat)
    (hl : xs.length=14) :
    let h := gap+1+((encode xs).length : Int)-1
    downHolds (before back gap (encode xs)) (h-((encode xs.reverse).length : Int)) [false] ∧
    silentSegment machine (cfg 83 h (before back gap (encode xs)))
      (cfg 92 (h-((encode xs.reverse).length : Int)) (before back gap (encode xs)))
      (encode xs.reverse).length := by
  dsimp only
  have hd := down_before_reverse back gap (encode xs)
  have he : (encode xs).reverse ++ [false,false] = false :: (encode xs.reverse ++ [false]) := by
    calc
      (encode xs).reverse ++ [false,false] = ((encode xs).reverse ++ [false]) ++ [false] := by simp [List.append_assoc]
      _ = (false :: encode xs.reverse) ++ [false] := by rw [encode_reverse]
      _ = false :: (encode xs.reverse ++ [false]) := rfl
  rw [he] at hd
  have ht : downHolds (before back gap (encode xs))
      (gap+1+((encode xs).length : Int)-1) (encode xs.reverse ++ [false]) := hd.2
  exact selector_on_values xs.reverse _ _ [false] (by simpa using hl) ht

end Shared.Beeping.NPcoNP.NativeHalfSelectorExact
#print axioms Shared.Beeping.NPcoNP.NativeHalfSelectorExact.selector_before_encoded

namespace Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn

theorem encode_length_reverse (xs : List Nat) :
    (encode xs.reverse).length=(encode xs).length := by
  induction xs with
  | nil => rfl
  | cons n ns ih =>
    simp [encode_append,encode,ih,Nat.add_comm]

/-- On a fourteen-value physical bank, the selector scans exactly those
blocks in reverse, then scans the two-zero gap and first one, reaching state
93 at a fixed head position with the entire tape unchanged. -/
theorem selector_bank_to93 (back : Int → Bool) (gap : Int) (xs : List Nat)
    (hl : xs.length=14) :
    silentSegment machine
      (cfg 83 (gap+((encode xs).length : Int)) (before back gap (encode xs)))
      (cfg 93 (gap+3) (before back gap (encode xs))) ((encode xs).length+3) := by
  let t := before back gap (encode xs)
  have hlen : (encode xs.reverse).length=(encode xs).length := encode_length_reverse xs
  have hs := (selector_before_encoded back gap xs hl).2
  have hs' : silentSegment machine (cfg 83 (gap+((encode xs).length : Int)) t)
      (cfg 92 gap t) (encode xs).length := by
    rw [hlen] at hs
    have hstart : gap+1+((encode xs).length : Int)-1=gap+((encode xs).length : Int) := by omega
    rw [hstart] at hs
    simpa only [add_sub_cancel_right] using hs
  have hz0 : t gap=false := (gap_cells back gap (encode xs)).1
  have hz1 : t (gap+1)=false := (gap_cells back gap (encode xs)).2.1
  have hone : t (gap+2)=true := by
    have hne : xs≠[] := by intro h; simp [h] at hl
    cases xs with
    | nil => contradiction
    | cons x xs =>
      have hb := before_suffix_bit back gap (encode (x::xs)) 0
      simpa [t,encode,block,bitAt,List.replicate_succ] using hb
  have h1 := oneSeg machine _ _ (step92_zero gap t hz0)
  have h2 := oneSeg machine _ _ (step92_zero (gap+1) t hz1)
  have h3 := oneSeg machine _ _ (step92_one (gap+2) t hone)
  have h23 : silentSegment machine (cfg 92 gap t) (cfg 92 (gap+2) t) 2 := by
    simpa [Int.add_assoc] using segAdd machine _ _ _ 1 1 h1 h2
  have hlast : silentSegment machine (cfg 92 gap t) (cfg 93 (gap+3) t) 3 := by
    simpa [Int.add_assoc] using segAdd machine _ _ _ 2 1 h23 h3
  exact segAdd machine _ _ _ (encode xs).length 3 hs' hlast

end Shared.Beeping.NPcoNP.NativeHalfSelectorExact
#print axioms Shared.Beeping.NPcoNP.NativeHalfSelectorExact.selector_bank_to93
