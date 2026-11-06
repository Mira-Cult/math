import Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
import Shared.Beeping.NPcoNP.Bootstrap284BankDecode

/-! A fixed-duration deterministic segment that preserves every supplied finite
suffix preserves the entire right-hand tape. The fixed duration is essential. -/
namespace Shared.Beeping.NPcoNP.NativeUniformSuffixFrame
open Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
set_option autoImplicit false

theorem readCells_length (t : Int → Bool) (start : Int) (n : Nat) :
    (readCells t start n).length=n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [readCells,ih]

theorem holds_readCells (t : Int → Bool) (start : Int) (n : Nat) :
    Holds t start (readCells t start n) := by
  induction n generalizing start with
  | zero => trivial
  | succ n ih => exact ⟨rfl,ih (start+1)⟩

/-- If the same deterministic duration admits a suffix-preserving proof for
every finite observation, it preserves every cell of that suffix. -/
theorem frame_of_uniform_suffix {n : Nat} (M : Machine n) (c e : Config n)
    (steps : Nat) (start : Int) (segment : silentSegment M c e steps)
    (suffix : ∀ xs, Holds c.tape start xs →
      ∃ out : Config n, silentSegment M c out steps ∧ Holds out.tape start xs) :
    ∀ q, start≤q → e.tape q=c.tape q := by
  intro q hq
  let i := (q-start).toNat
  let xs := readCells c.tape start (i+1)
  have hi : i<xs.length := by simp [xs,readCells_length]
  have hc : Holds c.tape start xs := holds_readCells c.tape start (i+1)
  obtain ⟨out,hseg,hout⟩ := suffix xs hc
  have he : out=e := hseg.1.symm.trans segment.1
  subst out
  have h1 := holds_get e.tape start xs hout i hi
  have h2 := holds_get c.tape start xs hc i hi
  have hcast : ((i : Nat) : Int)=q-start := Int.toNat_of_nonneg (by omega)
  have hpos : start+((i : Nat) : Int)=q := by omega
  rw [hpos] at h1 h2
  exact h1.trans h2.symm

#print axioms frame_of_uniform_suffix
end Shared.Beeping.NPcoNP.NativeUniformSuffixFrame
