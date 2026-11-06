import Shared.Beeping.NPcoNP.Bootstrap284BankPrefix

/-! An explicit unary-word view of the entire checked physical bootstrap
configuration. This representation equality does not identify the graph
program counter or prove a subsequent machine simulation. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

open Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284FirstExit

def windowTape (h : Int) (xs : List Bool) (p : Int) : Bool :=
  if h≤p ∧ p<h+(xs.length : Int) then xs[(p-h).toNat]?.getD false else false

theorem holds_get (t : Int → Bool) (h : Int) (xs : List Bool)
    (hx : Holds t h xs) (i : Nat) (hi : i<xs.length) :
    t (h+(i : Int)) = xs[i] := by
  induction xs generalizing h i with
  | nil => simp at hi
  | cons x xs ih =>
    change t h=x ∧ Holds t (h+1) xs at hx
    cases i with
    | zero => simpa using hx.1
    | succ i =>
      have hi' : i<xs.length := by simp at hi; omega
      have hh := ih (h+1) hx.2 i hi'
      simpa [Int.add_assoc, Int.add_comm, Int.add_left_comm] using hh

/-- A finite word and a blank exterior uniquely determine the whole tape. -/
theorem tape_eq_window (t : Int → Bool) (h : Int) (xs : List Bool)
    (hx : Holds t h xs)
    (hz : ∀ p, p<h ∨ h+(xs.length : Int)≤p → t p=false) :
    t = windowTape h xs := by
  funext p
  by_cases hin : h≤p ∧ p<h+(xs.length : Int)
  · have hn : 0≤p-h := by omega
    have hnat : (((p-h).toNat : Nat) : Int)=p-h := Int.toNat_of_nonneg hn
    have hi : (p-h).toNat<xs.length := by omega
    have he : h+(((p-h).toNat : Nat) : Int)=p := by omega
    have hh := holds_get t h xs hx (p-h).toNat hi
    simp only [he] at hh
    simp only [windowTape,hin,if_true,List.getElem?_eq_getElem hi,Option.getD_some]
    exact hh
  · have hout : p<h ∨ h+(xs.length : Int)≤p := by omega
    simp [windowTape,hin,hz p hout]

def bootstrapWord : List Bool :=
  encode (List.replicate 1909 0 ++ [1]) ++ [true,true,true,true]

theorem bootstrapWord_length : bootstrapWord.length=3825 := by
  change (encode (List.replicate 1909 0 ++ [1]) ++ [true,true,true,true]).length=3825
  rw [encode_append,encode_single,List.length_append,List.length_append,zeros_length,block_length]
  decide

/-- The exact blank-start configuration, with the full tape presented as a
unary-bank word surrounded by zeros. -/
theorem run_as_unary_window : machine.system.run 2133492 =
    cfg 261 (-2) (windowTape (-3821) bootstrapWord) := by
  have hw : Holds (machine.system.run 2133492).tape (-3821) bootstrapWord := blank_start_bank
  have hz : ∀ p, p<(-3821) ∨ (-3821)+(bootstrapWord.length : Int)≤p →
      (machine.system.run 2133492).tape p=false := by
    intro p hp
    have hl : (bootstrapWord.length : Int)=3825 := by rw [bootstrapWord_length]; rfl
    apply blank_start_exterior p
    omega
  have ht := tape_eq_window (machine.system.run 2133492).tape (-3821) bootstrapWord hw hz
  have hs := first_exit_state
  have hh := first_exit_head
  cases hc : machine.system.run 2133492 with
  | mk state head tape =>
    simp only [hc,cfg] at hs hh ht ⊢
    cases hs
    cases hh
    cases ht
    rfl

end Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

#print axioms Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape.run_as_unary_window
