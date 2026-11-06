import Shared.Beeping.Machines
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-! A finite-speed bound for every blank-start binary transition-flag machine. -/
namespace Shared.Beeping.Machines
set_option autoImplicit false

/-- After `t` transitions the head is at most `t` cells from its initial
position, and cells outside that interval still contain the blank symbol. -/
theorem Machine.run_lightCone {n : Nat} (M : Machine n) (t : Nat) :
    M.startHead-(t : Int) ≤ (M.system.run t).head ∧
    (M.system.run t).head ≤ M.startHead+(t : Int) ∧
    (∀ p : Int, p < M.startHead-(t : Int) → (M.system.run t).tape p=M.blank) ∧
    (∀ p : Int, M.startHead+(t : Int) < p → (M.system.run t).tape p=M.blank) := by
  induction t with
  | zero => simp [Machine.system,Machine.initial,EventSystem.run]
  | succ t ih =>
    obtain ⟨hl,hr,htl,htr⟩ := ih
    let c := M.system.run t
    let row := M.table.row c.state (c.tape c.head)
    change M.startHead-(t : Int) ≤ c.head at hl
    change c.head ≤ M.startHead+(t : Int) at hr
    have hhead : ((M.step c).1).head = row.move.apply c.head := rfl
    have hmove : c.head-1 ≤ ((M.step c).1).head ∧ ((M.step c).1).head ≤ c.head+1 := by
      rw [hhead]
      cases row.move <;> simp [Move.apply] <;> omega
    change M.startHead-((t+1 : Nat) : Int) ≤ ((M.step c).1).head ∧
      ((M.step c).1).head ≤ M.startHead+((t+1 : Nat) : Int) ∧
      (∀ p : Int, p < M.startHead-((t+1 : Nat) : Int) → ((M.step c).1).tape p=M.blank) ∧
      (∀ p : Int, M.startHead+((t+1 : Nat) : Int) < p → ((M.step c).1).tape p=M.blank)
    refine ⟨by push_cast; omega,by push_cast; omega,?_,?_⟩
    · intro p hp
      have hp' : p < M.startHead-(t : Int) := by push_cast at hp; omega
      have hne : p ≠ c.head := by dsimp [c] at *; omega
      change c.write row.write p=M.blank
      rw [Config.write_other c row.write p hne]
      exact htl p hp'
    · intro p hp
      have hp' : M.startHead+(t : Int) < p := by push_cast at hp; omega
      have hne : p ≠ c.head := by dsimp [c] at *; omega
      change c.write row.write p=M.blank
      rw [Config.write_other c row.write p hne]
      exact htr p hp'

#print axioms Machine.run_lightCone
end Shared.Beeping.Machines
