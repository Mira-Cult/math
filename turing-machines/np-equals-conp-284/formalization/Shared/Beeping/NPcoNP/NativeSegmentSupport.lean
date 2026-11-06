import Shared.Beeping.NPcoNP.NativeHalfScan

/-! A finite literal-machine segment preserves an eventual blank tail on an
arbitrary starting tape. It does not create the right-hand one needed by a scan. -/
namespace Shared.Beeping.NPcoNP.NativeSegmentSupport
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.NativeHalfScan
set_option autoImplicit false

/-- A finite run can enlarge, but cannot destroy, an eventual right blank tail. -/
theorem advance_right_blank {n : Nat} (M : Machine n) (c : Config n) (k : Nat)
    (initial : ∃ b : Int, ∀ q, b≤q → c.tape q=false) :
    ∃ b : Int, ∀ q, b≤q → ((W M).advance c k).tape q=false := by
  induction k with
  | zero => simpa [WordEventSystem.advance] using initial
  | succ k ih =>
    obtain ⟨b,hb⟩ := ih
    let d := (W M).advance c k
    refine ⟨max b (d.head+1),?_⟩
    intro q hq
    have hne : q≠d.head := by have := le_max_right b (d.head+1); omega
    have hbase : b≤q := le_trans (le_max_left _ _) hq
    change ((M.step d).1).tape q=false
    change d.write (M.table.row d.state (d.tape d.head)).write q=false
    rw [Config.write_other _ _ _ hne]
    exact hb q hbase

/-- Silence is irrelevant to the support argument; any certified silent
segment is in particular a finite advance. -/
theorem silent_right_blank {n : Nat} (M : Machine n) (c e : Config n) (k : Nat)
    (initial : ∃ b : Int, ∀ q, b≤q → c.tape q=false)
    (segment : silentSegment M c e k) :
    ∃ b : Int, ∀ q, b≤q → e.tape q=false := by
  have h := advance_right_blank M c k initial
  rw [segment.1] at h
  exact h

#print axioms advance_right_blank
#print axioms silent_right_blank
end Shared.Beeping.NPcoNP.NativeSegmentSupport
