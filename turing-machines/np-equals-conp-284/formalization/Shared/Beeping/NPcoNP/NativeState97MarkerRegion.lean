import Shared.Beeping.NPcoNP.NativeState97Characterization

/-! An inductive finite-state region proves eleven of the twelve state-97
erasing-source obligations. State 98 remains a separate hypothesis. -/
namespace Shared.Beeping.NPcoNP.NativeState97MarkerRegion
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeState97EntryInvariant
open Shared.Beeping.NPcoNP.NativeState97Characterization
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 50000000

/-- This fixed, checked table-state mask contains 234 states. -/
def regionMask : Nat := 15541062120751096226131918021409569568121252950535390730562542354841739278555078057888

def marked (q : Fin 284) : Bool := regionMask.testBit q.val

/-- Every row entering the region moves right and either writes a new one
or originates in the region, so a strict-left marker is preserved. -/
theorem checked_rows (q : Fin 284) (b : Bool)
    (h : marked (machine.table.row q b).next=true) :
    (machine.table.row q b).move=.right ∧
      ((machine.table.row q b).write=true ∨ marked q=true) := by
  have hall : ∀ (q : Fin 284) (b : Bool), marked (machine.table.row q b).next=true →
      (machine.table.row q b).move=.right ∧
        ((machine.table.row q b).write=true ∨ marked q=true) := by decide
  exact hall q b h

theorem marked_initial_false : marked 0=false := by decide

def RegionInvariant (c : Config 284) : Prop :=
  marked c.state=true → ∃ p : Int, p<c.head ∧ c.tape p=true

theorem step_region (c : Config 284) (ih : RegionInvariant c) :
    RegionInvariant (machine.step c).1 := by
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

theorem run_region (time : Nat) : RegionInvariant (machine.system.run time) := by
  induction time with
  | zero =>
    intro hs
    have hstate : (machine.system.run 0).state=0 := by
      apply Fin.ext
      exact machine_starts_zero.1
    rw [hstate,marked_initial_false] at hs
    contradiction
  | succ time ih =>
    change RegionInvariant (machine.step (machine.system.run time)).1
    exact step_region _ ih

/-- Eleven erasing source states are in the proved region; 98 is the only
exception. -/
theorem erasing_except_98_marked (q : Fin 284) (he : erasingSource q) (h98 : q≠98) :
    marked q=true := by
  have hall : ∀ q : Fin 284, erasingSource q → q≠98 → marked q=true := by decide
  exact hall q he h98

/-- The sole remaining erasing-entry obligation after the region proof. -/
def Safe98 : Prop :=
  ∀ time : Nat, (machine.system.run time).state=98 →
    (machine.system.run time).tape (machine.system.run time).head=true →
    ∃ p : Int, p<(machine.system.run time).head ∧ (machine.system.run time).tape p=true

theorem safe_entries_iff_safe98 : SafeErasingEntries ↔ Safe98 := by
  constructor
  · intro safe time hq hb
    apply safe time
    · rw [hq]
      decide
    · exact hb
  · intro safe time he hb
    by_cases h98 : (machine.system.run time).state=98
    · exact safe time h98 hb
    · exact run_region time (erasing_except_98_marked _ he h98)

/-- The only outstanding state-97 entry condition is the precise state-98
case; this equivalence does not assert it. -/
theorem marker_iff_safe98 : State97Marker ↔ Safe98 :=
  marker_iff_safe_entries.trans safe_entries_iff_safe98

theorem safe98_iff_every_97_returns : Safe98 ↔
    ∀ time : Nat, (machine.system.run time).state=97 →
      ∃ n : Nat, (machine.system.run (time+n)).state=83 :=
  safe_entries_iff_safe98.symm.trans safe_entries_iff_every_97_returns

#print axioms checked_rows
#print axioms run_region
#print axioms erasing_except_98_marked
#print axioms safe_entries_iff_safe98
#print axioms marker_iff_safe98
#print axioms safe98_iff_every_97_returns
end Shared.Beeping.NPcoNP.NativeState97MarkerRegion
