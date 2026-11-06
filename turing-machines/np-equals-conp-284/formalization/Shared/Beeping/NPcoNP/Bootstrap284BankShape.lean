import Shared.Beeping.NPcoNP.Bootstrap284FirstExit
import Shared.Beeping.NPcoNP.NativeHalfTapeScan

/-! Connect the actual boot snapshot to the shared unary-bank encoding.
This proves a finite tape window, not that the program counter or subsequent
primitive operations implement the register graph. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284BankShape

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot
open Shared.Beeping.NPcoNP.Bootstrap284BulkContinue7665
open Shared.Beeping.NPcoNP.Bootstrap284FirstExit

set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

theorem zeros_length (n : Nat) : (encode (List.replicate n 0)).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    change (encode (List.replicate n 0)).length + 2 = 2*(n+1)
    omega

theorem zeros_get (n i : Nat) (hi : i < (encode (List.replicate n 0)).length) :
    (encode (List.replicate n 0))[i] = (i % 2 == 0) := by
  induction n generalizing i with
  | zero => simp [encode] at hi
  | succ n ih =>
    simp only [List.replicate_succ, encode, block_zero, List.cons_append,
      List.nil_append, List.length_cons] at hi ⊢
    cases i with
    | zero => simp
    | succ i =>
      cases i with
      | zero => simp
      | succ i =>
        simp only [List.getElem_cons_succ]
        have hi' : i < (encode (List.replicate n 0)).length := by omega
        have hh := ih i hi'
        simpa [Nat.succ_eq_add_one, Nat.add_mod, Nat.add_assoc] using hh

theorem holds_append (t : Int → Bool) (h : Int) (xs ys : List Bool)
    (hx : Holds t h xs) (hy : Holds t (h+xs.length) ys) : Holds t h (xs++ys) := by
  induction xs generalizing h with
  | nil => simpa using hy
  | cons x xs ih =>
    simp only [Holds] at hx
    simp only [List.cons_append, Holds]
    refine ⟨hx.1, ih (h+1) hx.2 ?_⟩
    simpa [Int.add_assoc, Int.add_comm, Int.add_left_comm] using hy

def bootTape : Int → Bool := (toConfig (-4096) 4104 output7665).tape

/-- All 3,818 cells of the zero-register prefix are checked in the kernel. -/
theorem zero_bank_bits : ∀ i : Fin 3818,
    bootTape (-3821+(i.val : Int)) = (i.val % 2 == 0) := by decide

theorem zero_bank : Holds bootTape (-3821) (encode (List.replicate 1909 0)) := by
  apply holds_of_get
  intro i hi
  have hb := zeros_get 1909 i hi
  rw [hb]
  have hi' : i < 3818 := by have hl := zeros_length 1909; omega
  exact zero_bank_bits ⟨i,hi'⟩

theorem final_bank_cells : Holds bootTape (-3)
    [true,true,false,true,true,true,true] := by
  change bootTape (-3)=true ∧ bootTape (-2)=true ∧ bootTape (-1)=false ∧
    bootTape 0=true ∧ bootTape 1=true ∧ bootTape 2=true ∧ bootTape 3=true ∧ True
  decide

theorem left_margin_bits : ∀ i : Fin 275,
    bootTape (-4096+(i.val : Int))=false := by decide

theorem right_margin_bits : ∀ i : Fin 4,
    bootTape (4+(i.val : Int))=false := by decide

/-- The infinite tape is blank strictly left of the encoded bank. -/
theorem left_blank (p : Int) (hp : p < -3821) : bootTape p=false := by
  by_cases hlo : p < -4096
  · have hn : ¬ (-4096 : Int) ≤ p := by omega
    simp [bootTape,toConfig,cfg,bitSnapshot,hn]
  · have hnon : 0 ≤ p+4096 := by omega
    have hnat : (((p+4096).toNat : Nat) : Int)=p+4096 := Int.toNat_of_nonneg hnon
    have hi : (p+4096).toNat < 275 := by omega
    have he : (-4096 : Int)+(((p+4096).toNat : Nat) : Int)=p := by omega
    have hh := left_margin_bits ⟨(p+4096).toNat,hi⟩
    simpa only [he] using hh

/-- The infinite tape is blank strictly right of the four trailing ones. -/
theorem right_blank (p : Int) (hp : 3 < p) : bootTape p=false := by
  by_cases hhi : 8 ≤ p
  · have hn : ¬ p < (8 : Int) := by omega
    simp [bootTape,toConfig,cfg,bitSnapshot,hn]
  · have hnon : 0 ≤ p-4 := by omega
    have hnat : (((p-4).toNat : Nat) : Int)=p-4 := Int.toNat_of_nonneg hnon
    have hi : (p-4).toNat < 4 := by omega
    have he : (4 : Int)+(((p-4).toNat : Nat) : Int)=p := by omega
    have hh := right_margin_bits ⟨(p-4).toNat,hi⟩
    simpa only [he] using hh

/-- At the recorded physical bootstrap boundary, the actual tape contains
1,909 zero-valued unary blocks, one value-one block, and four trailing ones. -/
theorem blank_start_bank :
    Holds (machine.system.run 2133492).tape (-3821)
      (encode (List.replicate 1909 0 ++ [1]) ++ [true,true,true,true]) := by
  rw [run_first_exit]
  change Holds bootTape (-3821) _
  have hpos : (-3821 : Int) + (encode (List.replicate 1909 0)).length = -3 := by
    rw [zeros_length]
    norm_num
  have hlast : Holds bootTape
      ((-3821 : Int)+(encode (List.replicate 1909 0)).length)
      (block 1 ++ [true,true,true,true]) := by
    rw [hpos]
    exact final_bank_cells
  have hjoined := holds_append bootTape (-3821) (encode (List.replicate 1909 0))
    (block 1 ++ [true,true,true,true]) zero_bank hlast
  rw [encode_append, encode_single, List.append_assoc]
  exact hjoined

theorem blank_start_exterior (p : Int) (hp : p < -3821 ∨ 3 < p) :
    (machine.system.run 2133492).tape p=false := by
  rw [run_first_exit]
  change bootTape p=false
  rcases hp with hleft | hright
  · exact left_blank p hleft
  · exact right_blank p hright

end Shared.Beeping.NPcoNP.Bootstrap284BankShape

#print axioms Shared.Beeping.NPcoNP.Bootstrap284BankShape.blank_start_bank
#print axioms Shared.Beeping.NPcoNP.Bootstrap284BankShape.blank_start_exterior
