import Shared.Beeping.NPcoNP.NativeHalfScan

/-! Positive finite progress for an arbitrary literal-machine state that
scans ones to the right and exits on zero, without modifying the tape or
emitting events. The right-zero tail is explicit. -/
namespace Shared.Beeping.NPcoNP.PhysicalOnesScan

open Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.NativeHalfScan

theorem tail {states : Nat} (M : Machine states) (scan exit : Fin states)
    (one : ∀ h tape, tape h = true →
      M.step (cfg scan h tape) = (cfg scan (h+1) tape, false))
    (zero : ∀ h tape, tape h = false →
      M.step (cfg scan h tape) = (cfg exit (h+1) tape, false))
    (k : Nat) (h : Int) (tape : Int → Bool)
    (hz : ∀ p ≥ h+(k : Int), tape p=false) :
    ∃ m : Nat, 0<m ∧ m≤k+1 ∧
      silentSegment M (cfg scan h tape) (cfg exit (h+m) tape) m := by
  induction k generalizing h with
  | zero =>
    have ht : tape h=false := hz h (by simp)
    exact ⟨1, by omega, by omega, by simpa using oneSeg M _ _ (zero h tape ht)⟩
  | succ k ih =>
    cases ht : tape h with
    | false =>
      exact ⟨1, by omega, by omega, by simpa using oneSeg M _ _ (zero h tape ht)⟩
    | true =>
      have hz' : ∀ p ≥ (h+1)+(k : Int), tape p=false := by
        intro p hp
        apply hz p
        push_cast at *
        omega
      obtain ⟨m, hm, hbound, hseg⟩ := ih (h+1) hz'
      refine ⟨1+m, by omega, by omega, ?_⟩
      have hall := segAdd M _ _ _ 1 m (oneSeg M _ _ (one h tape ht)) hseg
      simpa [Int.add_assoc, Int.add_comm, Int.add_left_comm] using hall

/-- Variant whose zero row changes the stopping cell. The output tape is
recorded explicitly by the supplied write operation. -/
theorem tail_write {states : Nat} (M : Machine states) (scan exit : Fin states)
    (write : Int → (Int → Bool) → (Int → Bool))
    (one : ∀ h tape, tape h = true →
      M.step (cfg scan h tape) = (cfg scan (h+1) tape, false))
    (zero : ∀ h tape, tape h = false →
      M.step (cfg scan h tape) = (cfg exit (h+1) (write h tape), false))
    (k : Nat) (h : Int) (tape : Int → Bool)
    (hz : ∀ p ≥ h+(k : Int), tape p=false) :
    ∃ (m : Nat) (p : Int), 0<m ∧ m≤k+1 ∧ h≤p ∧ p≤h+k ∧
      silentSegment M (cfg scan h tape) (cfg exit (p+1) (write p tape)) m := by
  induction k generalizing h with
  | zero =>
    have ht : tape h=false := hz h (by simp)
    exact ⟨1,h,by omega,by omega,by omega,by omega,oneSeg M _ _ (zero h tape ht)⟩
  | succ k ih =>
    cases ht : tape h with
    | false =>
      exact ⟨1,h,by omega,by omega,by omega,by omega,oneSeg M _ _ (zero h tape ht)⟩
    | true =>
      have hz' : ∀ p ≥ (h+1)+(k : Int), tape p=false := by
        intro p hp
        apply hz p
        push_cast at *
        omega
      obtain ⟨m,p,hm,hbound,hlo,hhi,hseg⟩ := ih (h+1) hz'
      refine ⟨1+m,p,by omega,by omega,by omega,by omega,?_⟩
      exact segAdd M _ _ _ 1 m (oneSeg M _ _ (one h tape ht)) hseg

end Shared.Beeping.NPcoNP.PhysicalOnesScan

#print axioms Shared.Beeping.NPcoNP.PhysicalOnesScan.tail
#print axioms Shared.Beeping.NPcoNP.PhysicalOnesScan.tail_write
