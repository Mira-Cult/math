import Shared.Beeping.NPcoNP.NativeReturnReachableProgress
import Shared.Beeping.NPcoNP.NativeSelectorEntryProgress

/-! Composition of the proved return-marker invariant with the literal
selector chain. This is not yet a graph-operation or table compiler proof. -/
namespace Shared.Beeping.NPcoNP.NativeReturnSelectorProgress
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeReturnReachableProgress
open Shared.Beeping.NPcoNP.NativeSelectorEntryProgress
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem continue_to_93 (time n : Nat) (c : Config 284)
    (hn : 0<n) (hc : c.state=83)
    (hs : silentSegment machine (machine.system.run time) c n) :
    ∃ (duration : Nat) (e : Config 284), 0<duration ∧ e.state=93 ∧
      silentSegment machine (machine.system.run time) e duration := by
  have hrun : machine.system.run (time+n)=c := by
    rw [EventSystem.run_add, ← ScalarWordRefinement.advance_ofBeep]
    exact hs.1
  have h83 : (machine.system.run (time+n)).state=83 := by rw [hrun]; exact hc
  obtain ⟨m,e,hm,he,_,hmore⟩ := reachable_83_to_93 (time+n) h83
  refine ⟨n+m,e,by omega,he,?_⟩
  apply segAdd machine _ _ _ n m hs
  rw [← hrun]
  exact hmore

theorem reachable_28_to_93 (time : Nat)
    (h : (machine.system.run time).state=28) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=93 ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨n,c,hn,hc,hs⟩ := reachable_28_to_83 time h
  exact continue_to_93 time n c hn hc hs

theorem reachable_14_to_93 (time : Nat)
    (h : (machine.system.run time).state=14) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=93 ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨n,c,hn,hc,hs⟩ := reachable_14_to_83 time h
  exact continue_to_93 time n c hn hc hs

theorem reachable_261_one_to_93 (time : Nat)
    (h : (machine.system.run time).state=261)
    (one : (machine.system.run time).tape (machine.system.run time).head=true) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=93 ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨n,c,hn,hc,hs⟩ := reachable_261_one_to_83 time h one
  exact continue_to_93 time n c hn hc hs

#print axioms reachable_28_to_93
#print axioms reachable_14_to_93
#print axioms reachable_261_one_to_93
end Shared.Beeping.NPcoNP.NativeReturnSelectorProgress
