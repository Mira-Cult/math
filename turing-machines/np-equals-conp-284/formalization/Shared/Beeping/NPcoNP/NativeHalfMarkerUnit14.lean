import Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
import Shared.Beeping.NPcoNP.NativeHalfState12Progress

/-! Exact unit-selector continuation through the following state-12 scan. -/
namespace Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState12Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

theorem marker_three_blocks (k v y z w : Nat) (ws : List Nat) :
    ∃ tail, markerWindow (List.replicate k 0 ++ v :: y :: z :: w :: ws) =
      false :: (encode (List.replicate k 0) ++ block v ++ block y ++ block z ++ tail) := by
  obtain ⟨tail, ht⟩ := encode_ends_zero (w::ws) (by simp)
  refine ⟨tail, ?_⟩
  apply List.append_cancel_right (bs := [false])
  have hm := markerWindow_append_zero (List.replicate k 0 ++ v :: y :: z :: w :: ws)
  rw [encode_append] at hm
  change markerWindow (List.replicate k 0 ++ v :: y :: z :: w :: ws) ++ [false] =
    false :: (encode (List.replicate k 0) ++ (block v ++ (block y ++ (block z ++ encode (w::ws))))) at hm
  rw [ht] at hm
  simpa [List.append_assoc] using hm

/-- Exact state-12 scan of one encoded unary block. -/
theorem scan12 (n : Nat) (h : Int) (t : Int → Bool)
    (ht : Holds t h (List.replicate n true ++ [false])) :
    silentSegment machine (cfg 12 h t) (cfg 14 (h+(n : Int)+1) t) (n+1) := by
  induction n generalizing h with
  | zero =>
    simp only [List.replicate_zero,List.nil_append,Holds] at ht
    simpa using oneSeg machine _ _ (step12_zero h t ht.1)
  | succ n ih =>
    simp only [List.replicate_succ,List.cons_append,Holds] at ht
    have hs := oneSeg machine _ _ (step12_one h t ht.1)
    have hr := ih (h+1) ht.2
    have hall := segAdd machine _ _ _ 1 (n+1) hs hr
    simpa [Int.add_assoc,Int.add_comm,Int.add_left_comm,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using hall

/-- Unit selector followed by two full unary blocks reaches state 14 with
an exact head and a single charged tape write. -/
theorem marker_unit_to14 (t : Int → Bool) (a : Int) (k y z w : Nat) (ws : List Nat)
    (hw : Holds t a (markerWindow (List.replicate k 0 ++ 1 :: y :: z :: w :: ws))) :
    let d := a+((2*k : Nat) : Int)+4
    silentSegment machine (cfg 93 a t)
      (cfg 14 (d+(y : Int)+(z : Int)+4) (clearAt d t)) (2*k+y+z+8) := by
  dsimp only
  let d := a+((2*k : Nat) : Int)+4
  have h12 := marker_unit_to12 t a k y z (w::ws) hw
  obtain ⟨tail,he⟩ := marker_three_blocks k 1 y z w ws
  rw [he] at hw
  let pre := encode (List.replicate k 0) ++ block 1 ++ block y
  have hh := holds_append_tail t (a+1) pre (block z ++ tail) (by
    simpa [pre,List.append_assoc] using hw.2)
  have hpLen : pre.length=2*k+y+5 := by
    dsimp [pre]
    simp [zeros_length,block_length]
    omega
  rw [hpLen] at hh
  have hpos : a+1+((2*k+y+5 : Nat) : Int) = d+(y : Int)+2 := by
    dsimp [d]; push_cast; omega
  rw [hpos] at hh
  have hblock : Holds t (d+(y : Int)+2) (block z) :=
    holds_prefix_word t _ _ _ hh
  have hblock' : Holds (clearAt d t) (d+(y : Int)+2)
      (List.replicate (z+1) true ++ [false]) := by
    apply holds_clear_left
    · omega
    · simpa [block] using hblock
  have hnext := scan12 (z+1) (d+(y : Int)+2) (clearAt d t) hblock'
  have hjoined := segAdd machine _ _ _ (2*k+y+6) (z+1+1) h12 hnext
  have hend : d+(y : Int)+2+((z+1 : Nat) : Int)+1 = d+(y : Int)+(z : Int)+4 := by
    push_cast; omega
  have hcost : 2*k+y+6+(z+1+1)=2*k+y+z+8 := by omega
  simpa only [hend,hcost] using hjoined

#print axioms marker_unit_to14
end Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14
