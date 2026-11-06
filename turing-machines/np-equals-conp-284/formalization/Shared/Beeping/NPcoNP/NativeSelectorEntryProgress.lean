import Shared.Beeping.NPcoNP.NativeHalfSelectorReturn

/-! Every actual state-83 entry carries a physical right-hand one. This
supplies the marker needed after the finite selector chain. -/
namespace Shared.Beeping.NPcoNP.NativeSelectorEntryProgress
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 20000000

theorem enters83_writes_one_left (q : Fin 284) (b : Bool)
    (h : (machine.table.row q b).next=83) :
    (machine.table.row q b).write=true ∧ (machine.table.row q b).move=.left := by
  have hall : ∀ (q : Fin 284) (b : Bool), (machine.table.row q b).next=83 →
      (machine.table.row q b).write=true ∧ (machine.table.row q b).move=.left := by decide
  exact hall q b h

/-- Every blank-start state-83 visit has a one immediately to the right. -/
theorem reachable_83_right_one (time : Nat)
    (hstate : (machine.system.run time).state=83) :
    (machine.system.run time).tape ((machine.system.run time).head+1)=true := by
  cases time with
  | zero =>
    have hs : (machine.system.run 0).state.val=0 := machine_starts_zero.1
    have hv := congrArg Fin.val hstate
    rw [hs] at hv
    contradiction
  | succ time =>
    let c := machine.system.run time
    let r := machine.table.row c.state (c.tape c.head)
    have hn : r.next=83 := by
      change ((machine.step c).1).state=83 at hstate
      exact hstate
    obtain ⟨hw,hm⟩ := enters83_writes_one_left c.state (c.tape c.head) hn
    change ((machine.step c).1).tape (((machine.step c).1).head+1)=true
    simp [Machine.step,r,hm,hw,Move.apply,Config.write]

/-- Every actual state-83 visit returns to state 93 through the complete
selector scan, in finite positive time with no beep or tape change. -/
theorem reachable_83_to_93 (time : Nat)
    (hstate : (machine.system.run time).state=83) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=93 ∧
      e.tape=(machine.system.run time).tape ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨n,hn,hs⟩ := reachable_83_to_92 time hstate
  let h := (machine.system.run time).head
  let tape := (machine.system.run time).tape
  let h92 : Int := h-(n : Int)
  have hm : tape (h+1)=true := reachable_83_right_one time hstate
  have heq : h92+((n+1 : Nat) : Int)=h+1 := by dsimp [h92]; push_cast; omega
  have hone : tape (h92+((n+1 : Nat) : Int))=true := by rw [heq]; exact hm
  obtain ⟨m,hmpos,_,hmore⟩ := scan92_to_one (n+1) h92 tape hone
  refine ⟨n+m,cfg 93 (h92+(m : Int)) tape,by omega,rfl,rfl,?_⟩
  exact segAdd machine _ _ _ n m hs hmore

#print axioms enters83_writes_one_left
#print axioms reachable_83_right_one
#print axioms reachable_83_to_93
end Shared.Beeping.NPcoNP.NativeSelectorEntryProgress
