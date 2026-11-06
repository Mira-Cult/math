import Shared.Beeping.NPcoNP.NativeControlMarkerInvariant
import Shared.Beeping.NPcoNP.NativeState10LeftMarker
import Shared.Beeping.NPcoNP.NativeHalfSelectorBound

/-! Exact reduction of the reachable state-97 marker invariant to the
finite family of erasing-entry obligations. This does not assert those
obligations or the physical/graph refinement. -/
namespace Shared.Beeping.NPcoNP.NativeState97EntryInvariant
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeControlMarkerInvariant
open Shared.Beeping.NPcoNP.NativeState10LeftMarker
open Shared.Beeping.NPcoNP.NativeHalfSelectorBound
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 30000000

/-- Source states whose `true` row erases the read one, moves left, and
enters state 97. -/
def erasingSource (q : Fin 284) : Prop :=
  q.val ∈ ([98,100,102,113,164,179,186,191,192,202,206,226] : List Nat)

instance (q : Fin 284) : Decidable (erasingSource q) := by
  unfold erasingSource
  infer_instance

/-- Exhaustive classification of the fixed table's incoming state-97 rows. -/
theorem incoming97 (q : Fin 284) (b : Bool)
    (hn : (machine.table.row q b).next=97) :
    (q=6 ∧ b=false) ∨ (q=10 ∧ b=true) ∨ (q=97 ∧ b=false) ∨
      (erasingSource q ∧ b=true) := by
  have hall : ∀ (q : Fin 284) (b : Bool), (machine.table.row q b).next=97 →
      (q=6 ∧ b=false) ∨ (q=10 ∧ b=true) ∨ (q=97 ∧ b=false) ∨
        (erasingSource q ∧ b=true) := by decide
  exact hall q b hn

/-- Each of the twelve source-state `true` rows has exactly this effect. -/
theorem erasing_row (q : Fin 284) (hq : erasingSource q) :
    (machine.table.row q true).next=97 ∧
    (machine.table.row q true).write=false ∧
    (machine.table.row q true).move=.left := by
  have hall : ∀ q : Fin 284, erasingSource q →
      (machine.table.row q true).next=97 ∧
      (machine.table.row q true).write=false ∧
      (machine.table.row q true).move=.left := by decide
  exact hall q hq

/-- The unresolved predicate is required only when one of the erasing
rows is actually selected on the blank-start run. -/
def SafeErasingEntries : Prop :=
  ∀ time : Nat, erasingSource (machine.system.run time).state →
    (machine.system.run time).tape (machine.system.run time).head=true →
    ∃ p : Int, p<(machine.system.run time).head ∧ (machine.system.run time).tape p=true

/-- The marker condition needed to prevent state 97 scanning forever. -/
def State97Marker : Prop :=
  ∀ time : Nat, (machine.system.run time).state=97 →
    ∃ p : Int, p≤(machine.system.run time).head ∧ (machine.system.run time).tape p=true

/-- A strictly left marker survives any left-moving literal transition and
ends at or left of the new head, irrespective of what the transition writes. -/
theorem left_marker_after_step (c : Config 284)
    (hm : (machine.table.row c.state (c.tape c.head)).move=.left)
    (hp : ∃ p : Int, p<c.head ∧ c.tape p=true) :
    ∃ p : Int, p≤(machine.step c).1.head ∧ (machine.step c).1.tape p=true := by
  obtain ⟨p,hp,ht⟩ := hp
  let row := machine.table.row c.state (c.tape c.head)
  refine ⟨p,?_,?_⟩
  · change p≤row.move.apply c.head
    rw [hm]
    simp [Move.apply]
    omega
  · change c.write row.write p=true
    rw [Config.write_other _ _ _ (by omega)]
    exact ht

/-- The exact remaining marker invariant is equivalent to safety at the
twelve erasing source states. -/
theorem marker_iff_safe_entries : State97Marker ↔ SafeErasingEntries := by
  constructor
  · intro mark time hq hb
    let c := machine.system.run time
    have hq' : erasingSource c.state := hq
    have hb' : c.tape c.head=true := hb
    obtain ⟨hn,hw,hm⟩ := erasing_row c.state hq'
    have hstep : (machine.step c).1.state=97 := by
      change (machine.table.row c.state (c.tape c.head)).next=97
      rw [hb']
      exact hn
    have hmnext : ∃ p : Int, p≤(machine.step c).1.head ∧ (machine.step c).1.tape p=true := by
      exact mark (time+1) hstep
    obtain ⟨p,hp,ht⟩ := hmnext
    have hpos : p<c.head := by
      change p≤(machine.table.row c.state (c.tape c.head)).move.apply c.head at hp
      rw [hb',hm] at hp
      simp [Move.apply] at hp
      omega
    have ht' : c.tape p=true := by
      change c.write (machine.table.row c.state (c.tape c.head)).write p=true at ht
      rw [Config.write_other _ _ _ (by omega)] at ht
      exact ht
    exact ⟨p,hpos,ht'⟩
  · intro safe time
    induction time with
    | zero =>
      intro h
      have hs : (machine.system.run 0).state.val=0 := machine_starts_zero.1
      have hv := congrArg Fin.val h
      rw [hs] at hv
      contradiction
    | succ time ih =>
      intro hnext
      let c := machine.system.run time
      let row := machine.table.row c.state (c.tape c.head)
      have hn : row.next=97 := hnext
      have hm : row.move=.left := by
        have hall : ∀ (q : Fin 284) (b : Bool), (machine.table.row q b).next=97 →
            (machine.table.row q b).move=.left := by decide
        exact hall c.state (c.tape c.head) hn
      have hp : ∃ p : Int, p<c.head ∧ c.tape p=true := by
        rcases incoming97 c.state (c.tape c.head) hn with h6 | h10 | h97 | herase
        · exact (run_control_invariant time).1 h6.1
        · have hh := reachable_10_left_one time h10.1
          exact hh
        · obtain ⟨p,hp,ht⟩ := ih h97.1
          change p≤c.head at hp
          change c.tape p=true at ht
          refine ⟨p,?_,ht⟩
          have hread : c.tape c.head=false := h97.2
          have hne : p≠c.head := by intro he; rw [he,hread] at ht; contradiction
          omega
        · exact safe time herase.1 herase.2
      exact left_marker_after_step c hm hp

/-- Once all twelve erasing-entry obligations are discharged, every actual
state-97 visit reaches state 93 within the quantitative silent bound. -/
theorem safe_entries_give_progress (safe : SafeErasingEntries) (time : Nat)
    (hstate : (machine.system.run time).state=97) :
    ∃ n : Nat, 0<n ∧ n≤6*time+33 ∧
      ∃ e : Config 284, e.state=93 ∧ e.tape=(machine.system.run time).tape ∧
        silentSegment machine (machine.system.run time) e n := by
  obtain ⟨p,hp,hm⟩ := marker_iff_safe_entries.mpr safe time hstate
  exact reachable_97_to_93_time_bound time hstate p hp hm

#print axioms incoming97
#print axioms erasing_row
#print axioms marker_iff_safe_entries
#print axioms safe_entries_give_progress
end Shared.Beeping.NPcoNP.NativeState97EntryInvariant
