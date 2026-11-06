import Shared.Beeping.NPcoNP.NativeReturnMarkerInvariant
import Shared.Beeping.NPcoNP.NativeHalfState93Marker

/-! State-6/7 marker invariant for the actual blank-start run. -/
namespace Shared.Beeping.NPcoNP.NativeControlMarkerInvariant
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
open Shared.Beeping.NPcoNP.NativeHalfState93Progress
open Shared.Beeping.NPcoNP.NativeHalfState93Marker
open Shared.Beeping.NPcoNP.NativeReturnMarkerInvariant
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 20000000

theorem incoming6 (q : Fin 284) (b : Bool) (h : (machine.table.row q b).next=6) :
    (q=7 ∧ b=false) ∨ (q=28 ∧ b=false) ∨ (q=93 ∧ b=false) := by
  have hall : ∀ (q : Fin 284) (b : Bool), (machine.table.row q b).next=6 →
      (q=7 ∧ b=false) ∨ (q=28 ∧ b=false) ∨ (q=93 ∧ b=false) := by decide
  exact hall q b h

theorem incoming7 (q : Fin 284) (b : Bool) (h : (machine.table.row q b).next=7) :
    q=6 ∧ b=true := by
  have hall : ∀ (q : Fin 284) (b : Bool), (machine.table.row q b).next=7 →
      q=6 ∧ b=true := by decide
  exact hall q b h

def ControlInvariant (c : Config 284) : Prop :=
  (c.state=6 → ∃ p : Int, p<c.head ∧ c.tape p=true) ∧
  (c.state=7 → ∃ p : Int, p<c.head-1 ∧ c.tape p=true)

theorem control_step (c : Config 284) (hi : ControlInvariant c)
    (h28 : c.state=28 → ∃ p : Int, p<c.head-1 ∧ c.tape p=true)
    (h93 : c.state=93 → c.tape (c.head-1)=true) :
    ControlInvariant (machine.step c).1 := by
  rcases c with ⟨q,h,tape⟩
  rcases hi with ⟨hi6,hi7⟩
  constructor
  · intro ht
    have hn : (machine.table.row q (tape h)).next=6 := ht
    rcases incoming6 q (tape h) hn with ⟨hq,hr⟩ | ⟨hq,hr⟩ | ⟨hq,hr⟩
    · subst q
      obtain ⟨p,hp,hm⟩ := hi7 rfl
      change p<h-1 at hp
      change tape p=true at hm
      have hs := step7_zero h tape hr
      change ∃ p : Int, p<(machine.step (cfg 7 h tape)).1.head ∧
        (machine.step (cfg 7 h tape)).1.tape p=true
      rw [hs]
      exact ⟨p,by simp only [cfg]; omega,hm⟩
    · subst q
      obtain ⟨p,hp,hm⟩ := h28 rfl
      change p<h-1 at hp
      change tape p=true at hm
      have hs := step28_zero h tape hr
      change ∃ p : Int, p<(machine.step (cfg 28 h tape)).1.head ∧
        (machine.step (cfg 28 h tape)).1.tape p=true
      rw [hs]
      exact ⟨p,by simp only [cfg]; omega,hm⟩
    · subst q
      have hm := h93 rfl
      change tape (h-1)=true at hm
      have hs := step93_zero h tape hr
      change ∃ p : Int, p<(machine.step (cfg 93 h tape)).1.head ∧
        (machine.step (cfg 93 h tape)).1.tape p=true
      rw [hs]
      exact ⟨h-1,by simp only [cfg]; omega,hm⟩
  · intro ht
    have hn : (machine.table.row q (tape h)).next=7 := ht
    obtain ⟨hq,hr⟩ := incoming7 q (tape h) hn
    subst q
    obtain ⟨p,hp,hm⟩ := hi6 rfl
    change p<h at hp
    change tape p=true at hm
    have hs := step6_one h tape hr
    change ∃ p : Int, p<(machine.step (cfg 6 h tape)).1.head-1 ∧
      (machine.step (cfg 6 h tape)).1.tape p=true
    rw [hs]
    exact ⟨p,by simp only [cfg]; omega,hm⟩

theorem run_control_invariant (time : Nat) : ControlInvariant (machine.system.run time) := by
  induction time with
  | zero =>
    constructor <;> intro h
    · have hs : (machine.system.run 0).state.val=0 := machine_starts_zero.1
      have hv := congrArg Fin.val h
      rw [hs] at hv
      contradiction
    · have hs : (machine.system.run 0).state.val=0 := machine_starts_zero.1
      have hv := congrArg Fin.val h
      rw [hs] at hv
      contradiction
  | succ time ih =>
    change ControlInvariant (machine.step (machine.system.run time)).1
    exact control_step _ ih (run_invariant time).2 (reachable_93_left_one time)

#print axioms run_control_invariant
end Shared.Beeping.NPcoNP.NativeControlMarkerInvariant
