import Shared.Beeping.NPcoNP.NativeHalfBankBridge
import Shared.Beeping.NPcoNP.UnarySuffixShift

/-! Connect the actual forward scan to the pinned producer's finite unary
suffix tape representation. This establishes only the silent scan to the
first double zero; the backward sweep and complete HALF remain separate. -/
namespace Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.Table284

theorem holds_of_get (tape : Int → Bool) (h : Int) (xs : List Bool)
    (ht : ∀ i, (hi : i < xs.length) → tape (h + (i : Int)) = xs[i]) : Holds tape h xs := by
  induction xs generalizing h with
  | nil => trivial
  | cons x xs ih =>
    constructor
    · have hh := ht 0 (by simp)
      change tape (h + 0) = x at hh
      simpa using hh
    · apply ih
      intro i hi
      have hh := ht (i+1) (by simp; omega)
      simpa [Int.add_assoc, Int.add_comm, Int.add_left_comm] using hh

theorem holds_before_suffix (base : Int → Bool) (gap : Int) (suffix : List Bool) :
    Holds (before base gap suffix) (gap+2) (suffix ++ [false]) := by
  apply holds_of_get
  intro i hi
  rw [before_suffix_bit]
  by_cases h : i < suffix.length
  · simp [bitAt, h]
  · have hle : i ≤ suffix.length := by simpa using hi
    have he : i = suffix.length := by omega
    subst i
    simp [bitAt]

theorem selected_before_bank (base : Int → Bool) (gap : Int) (x : Nat) (xs : List Nat) :
    silentSegment machine (cfg 32 (gap+2) (before base gap (UnaryBank.encode (x::xs))))
      (cfg 34 (gap+2 + (unaryBankPrefix x xs).length)
        (before base gap (UnaryBank.encode (x::xs)))) ((unaryBankPrefix x xs).length + 2) :=
  selected_encoded_scan x xs (gap+2) _ (holds_before_suffix base gap _)

end Shared.Beeping.NPcoNP.NativeHalfScan
