import Shared.Beeping.NPcoNP.NativeState97EntryInvariant

/-! The twelve erasing-entry obligations exactly characterize state-97
return progress. A violating reachable entry would force eventual silence;
no such violation is asserted. -/
namespace Shared.Beeping.NPcoNP.NativeState97Characterization
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState97Progress
open Shared.Beeping.NPcoNP.NativeState97EntryInvariant
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

/-- On an actual state-97 visit with no one at or left of the head, every
future step remains in state 97 and emits no beep. -/
theorem reachable_97_no_marker_stalls (time : Nat)
    (hstate : (machine.system.run time).state=97)
    (hnot : ¬ ∃ p : Int, p≤(machine.system.run time).head ∧
      (machine.system.run time).tape p=true) :
    ∀ n, (machine.system.run (time+n)).state=97 ∧
      ¬ machine.system.BeepAt (time+n) := by
  let c := machine.system.run time
  change ¬ ∃ p : Int, p≤c.head ∧ c.tape p=true at hnot
  have hz : ∀ i : Nat, c.tape (c.head-(i : Int))=false := by
    intro i
    cases he : c.tape (c.head-(i : Int)) with
    | false => rfl
    | true => exact False.elim (hnot ⟨_,by omega,he⟩)
  have hc : c=cfg 97 c.head c.tape := by
    have he : c=cfg c.state c.head c.tape := by cases c; rfl
    have hs : c.state=97 := hstate
    simpa only [hs] using he
  intro n
  have hs := zero_ray_silent c.head c.tape hz n
  constructor
  · rw [EventSystem.run_add]
    change (machine.system.advance c n).state=97
    rw [hc]
    exact hs.1
  · rw [EventSystem.beepAt_add_iff]
    change ¬ machine.system.BeepFrom c n
    rw [hc]
    exact hs.2

/-- Such a visit would make the literal table eventually silent. -/
theorem reachable_97_no_marker_eventuallySilent (time : Nat)
    (hstate : (machine.system.run time).state=97)
    (hnot : ¬ ∃ p : Int, p≤(machine.system.run time).head ∧
      (machine.system.run time).tape p=true) : machine.system.EventuallySilent := by
  apply (EventSystem.eventuallySilent_iff_shift machine.system time).2
  exact ⟨0,fun n _ => (reachable_97_no_marker_stalls time hstate hnot n).2⟩

/-- Exactly the erasing-entry obligations are needed for every reachable
state-97 visit to return to state 83. -/
theorem safe_entries_iff_every_97_returns : SafeErasingEntries ↔
    ∀ time : Nat, (machine.system.run time).state=97 →
      ∃ n : Nat, (machine.system.run (time+n)).state=83 := by
  constructor
  · intro safe time hstate
    obtain ⟨p,hp,hm⟩ := marker_iff_safe_entries.mpr safe time hstate
    obtain ⟨n,e,_,he,hs⟩ := reachable_97_to_83 time hstate p hp hm
    have hrun : machine.system.run (time+n)=e := by
      rw [EventSystem.run_add, ← ScalarWordRefinement.advance_ofBeep]
      exact hs.1
    exact ⟨n,by rw [hrun]; exact he⟩
  · intro returns
    apply marker_iff_safe_entries.mp
    intro time hstate
    by_contra hnot
    obtain ⟨n,hn⟩ := returns time hstate
    have hs := (reachable_97_no_marker_stalls time hstate hnot n).1
    rw [hn] at hs
    contradiction

/-- A violation of the erasing-entry obligations would make the selected
literal machine eventually silent. The existence of a violation is open. -/
theorem unsafe_entries_imply_eventuallySilent (hUnsafe : ¬ SafeErasingEntries) :
    machine.system.EventuallySilent := by
  by_contra hnot
  apply hUnsafe
  apply marker_iff_safe_entries.mp
  intro time hstate
  by_contra hmarker
  exact hnot (reachable_97_no_marker_eventuallySilent time hstate hmarker)

#print axioms reachable_97_no_marker_stalls
#print axioms safe_entries_iff_every_97_returns
#print axioms unsafe_entries_imply_eventuallySilent
end Shared.Beeping.NPcoNP.NativeState97Characterization
