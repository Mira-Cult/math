import Shared.Beeping.NPcoNP.NativeHalfState10Progress

/-! Finite checked state-set invariant supplying a left-hand one for every
actual state-10 visit. It does not supply a one to the right. -/
namespace Shared.Beeping.NPcoNP.NativeState10LeftMarker
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 30000000

def stateMask : Nat := 15539454000224823470129595521594288467413035586380649316585804248883200963139705243136

def marked (q : Fin 284) : Bool := stateMask.testBit q.val

/-- Every incoming row of the 51-state region moves right and either writes
a fresh marker or comes from the same region with its earlier marker intact. -/
theorem checked_rows (q : Fin 284) (b : Bool)
    (h : marked (machine.table.row q b).next=true) :
    (machine.table.row q b).move=.right ∧
      ((machine.table.row q b).write=true ∨ marked q=true) := by
  have hall : ∀ (q : Fin 284) (b : Bool), marked (machine.table.row q b).next=true →
      (machine.table.row q b).move=.right ∧
        ((machine.table.row q b).write=true ∨ marked q=true) := by decide
  exact hall q b h

theorem mark_initial_false : marked 0=false := by decide
theorem mark10 : marked 10=true := by decide

def LeftInvariant (c : Config 284) : Prop :=
  marked c.state=true → ∃ p : Int, p<c.head ∧ c.tape p=true

theorem step_invariant (c : Config 284) (ih : LeftInvariant c) :
    LeftInvariant (machine.step c).1 := by
  intro ht
  let row := machine.table.row c.state (c.tape c.head)
  have hn : marked row.next=true := ht
  obtain ⟨hright,hwrite⟩ := checked_rows c.state (c.tape c.head) hn
  rcases hwrite with hw | hs
  · refine ⟨c.head,?_,?_⟩
    · change c.head < row.move.apply c.head
      rw [hright]
      simp [Move.apply]
    · change c.write row.write c.head=true
      simpa using hw
  · obtain ⟨p,hp,hm⟩ := ih hs
    refine ⟨p,?_,?_⟩
    · change p < row.move.apply c.head
      rw [hright]
      simp only [Move.apply]
      omega
    · change c.write row.write p=true
      rw [Config.write_other _ _ _ (by omega)]
      exact hm

theorem run_invariant (time : Nat) : LeftInvariant (machine.system.run time) := by
  induction time with
  | zero =>
    intro hs
    have hstate : (machine.system.run 0).state=0 := by
      apply Fin.ext
      exact machine_starts_zero.1
    rw [hstate,mark_initial_false] at hs
    contradiction
  | succ time ih =>
    change LeftInvariant (machine.step (machine.system.run time)).1
    exact step_invariant _ ih

theorem reachable_10_left_one (time : Nat)
    (hstate : (machine.system.run time).state=10) :
    ∃ p : Int, p<(machine.system.run time).head ∧ (machine.system.run time).tape p=true := by
  have hs : marked (machine.system.run time).state=true := by rw [hstate]; exact mark10
  exact run_invariant time hs

#print axioms checked_rows
#print axioms reachable_10_left_one
end Shared.Beeping.NPcoNP.NativeState10LeftMarker
