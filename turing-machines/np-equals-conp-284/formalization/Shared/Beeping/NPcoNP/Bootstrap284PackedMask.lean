import Shared.Beeping.NPcoNP.Bootstrap284PackedScans

/-! A kernel-checked contiguous-bit mask for future packed scan acceleration.
This file does not yet replace the existing per-pair executor. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284PackedMask
open Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot
open Shared.Beeping.NPcoNP.Bootstrap284Scans
open Shared.Beeping.NPcoNP.Bootstrap284Effects

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Ones in the half-open bit interval `[offset,offset+count)`. -/
def intervalMask (offset count : Nat) : Nat := (2^count-1) <<< offset

/-- Exact bits of the interval mask, including empty and boundary cases. -/
theorem testBit_intervalMask (offset count j : Nat) :
    (intervalMask offset count).testBit j = decide (offset≤j ∧ j<offset+count) := by
  rw [intervalMask,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one]
  by_cases h : offset≤j
  · have he : (j-offset<count) ↔ j<offset+count := by omega
    simp [h,he]
  · have hn : ¬ (offset≤j ∧ j<offset+count) := by omega
    simp [h,hn]

/-- Toggling the interval flips exactly its bits and preserves all others. -/
theorem testBit_toggleInterval (bits offset count j : Nat) :
    (bits ^^^ intervalMask offset count).testBit j =
      if offset≤j ∧ j<offset+count then !(bits.testBit j) else bits.testBit j := by
  rw [Nat.testBit_xor,testBit_intervalMask]
  by_cases h : offset≤j ∧ j<offset+count <;> simp [h]

/-- A packed interval toggle agrees on the entire unbounded tape with
flipping exactly the corresponding cells. -/
theorem snapshot_toggleInterval (base h : Int) (span bits n : Nat)
    (hlo : base≤h-2*(n : Int)+1) (hhi : h<base+(span : Int)) :
    bitSnapshot base span (bits ^^^ intervalMask (h-2*(n : Int)+1-base).toNat (2*n)) =
      fun p => if h-2*(n : Int)+1≤p ∧ p≤h then !(bitSnapshot base span bits p)
        else bitSnapshot base span bits p := by
  funext p
  by_cases hp : base≤p ∧ p<base+(span : Int)
  · have hoff : (((h-2*(n : Int)+1-base).toNat : Nat) : Int)=h-2*(n : Int)+1-base :=
      Int.toNat_of_nonneg (by omega)
    have hj : (((p-base).toNat : Nat) : Int)=p-base := Int.toNat_of_nonneg (by omega)
    have he : ((h-2*(n : Int)+1-base).toNat≤(p-base).toNat ∧
        (p-base).toNat < (h-2*(n : Int)+1-base).toNat+2*n) ↔
        (h-2*(n : Int)+1≤p ∧ p≤h) := by omega
    simp only [bitSnapshot,if_pos hp,testBit_toggleInterval,he]
  · have hn : ¬ (h-2*(n : Int)+1≤p ∧ p≤h) := by omega
    simp only [bitSnapshot,if_neg hp,if_neg hn]

/-- On the guarded alternating pattern, flipping the contiguous interval is
exactly the existing pair-by-pair unbounded-tape rewrite. -/
theorem toggleTape_eq_leftEffect (n : Nat) (h : Int) (t : Int → Bool)
    (hs : ∀ i<n, t (h-2*(i : Int))=true ∧ t (h-2*(i : Int)-1)=false) :
    (fun p => if h-2*(n : Int)+1≤p ∧ p≤h then !(t p) else t p) = leftEffect n t h := by
  funext p
  by_cases hp : h-2*(n : Int)+1≤p ∧ p≤h
  · let d : Nat := (h-p).toNat
    have hd : (d : Int)=h-p := Int.toNat_of_nonneg (by omega)
    let i := d/2
    have hi : i<n := by dsimp [i]; omega
    have hpar : d%2=0 ∨ d%2=1 := by omega
    simp only [if_pos hp]
    rcases hpar with heven | hodd
    · have hpos : p=h-2*(i : Int) := by dsimp [i]; omega
      rw [hpos,(hs i hi).1,(leftEffect_pair n i h t hi).1]
      rfl
    · have hpos : p=h-2*(i : Int)-1 := by dsimp [i]; omega
      rw [hpos,(hs i hi).2,(leftEffect_pair n i h t hi).2]
      rfl
  · have ho : h<p ∨ p≤h-2*(n : Int) := by omega
    rw [leftEffect_outside n h p t ho]
    simp only [if_neg hp]

/-- A single contiguous packed XOR replaces all pair writes when the
literal scan's pattern and span checks hold. -/
theorem bulkLeft_correct (base h : Int) (span bits n : Nat)
    (hlo : base≤h-2*(n : Int)+1) (hhi : h<base+(span : Int))
    (hs : ∀ i<n, bitSnapshot base span bits (h-2*(i : Int))=true ∧
      bitSnapshot base span bits (h-2*(i : Int)-1)=false) :
    bitSnapshot base span (bits ^^^ intervalMask (h-2*(n : Int)+1-base).toNat (2*n)) =
      leftEffect n (bitSnapshot base span bits) h := by
  rw [snapshot_toggleInterval base h span bits n hlo hhi]
  exact toggleTape_eq_leftEffect n h (bitSnapshot base span bits) hs

end Shared.Beeping.NPcoNP.Bootstrap284PackedMask
