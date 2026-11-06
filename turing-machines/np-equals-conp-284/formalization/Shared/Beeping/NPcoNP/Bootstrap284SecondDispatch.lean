import Shared.Beeping.NPcoNP.Bootstrap284State97
import Shared.Beeping.NPcoNP.NativeHalfState10Progress

/-! Check the next 66 literal silent transitions and connect the resulting
state-261 zero branch to its marker-sensitive progress theorem. This is a
finite prefix, not a proof of the recurring graph simulation. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Progress
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284RunBridge
open Shared.Beeping.NPcoNP.Bootstrap284State97

set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

def after66 : Packed := (runSilent (-4096) 4104 66 after28).getD ⟨0,0,0⟩

theorem checked66 : runSilent (-4096) 4104 66 after28 = some after66 := by decide

theorem segment66 : silentSegment machine (toConfig (-4096) 4104 after28)
    (toConfig (-4096) 4104 after66) 66 :=
  runSilent_sound (-4096) 4104 66 after28 after66 checked66

theorem blank_start_66 : silentSegment machine (machine.system.run 0)
    (toConfig (-4096) 4104 after66) 2133586 := by
  have h := segAdd machine _ _ _ 2133520 66 blank_start_28 segment66
  simpa using h

theorem run_2133586 : machine.system.run 2133586 = toConfig (-4096) 4104 after66 :=
  run_of_initial_segment 2133586 _ blank_start_66

theorem state261 : (machine.system.run 2133586).state=261 := by rw [run_2133586]; decide
theorem head_neg2 : (machine.system.run 2133586).head=(-2) := by rw [run_2133586]; decide
theorem zero_neg2 : (machine.system.run 2133586).tape (-2)=false := by rw [run_2133586]; decide
theorem zero_neg1 : (machine.system.run 2133586).tape (-1)=false := by rw [run_2133586]; decide
theorem zero_0 : (machine.system.run 2133586).tape 0=false := by rw [run_2133586]; decide
theorem one_3 : (machine.system.run 2133586).tape 3=true := by rw [run_2133586]; decide

/-- The next zero-dispatch reaches state 83 in positive finite silent time;
the required zeros and marker are checked on the actual blank-start run. -/
theorem blank_start_second_dispatch_to83 :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=83 ∧
      silentSegment machine (machine.system.run 0) e (2133586+n) := by
  let t := (machine.system.run 2133586).tape
  have h0 : t (-2)=false := zero_neg2
  have h1 : t ((-2)+1)=false := by
    change (machine.system.run 2133586).tape (-1)=false
    exact zero_neg1
  have h2 : t ((-2)+1+1)=false := by
    change (machine.system.run 2133586).tape 0=false
    exact zero_0
  have hm : t (((-2)+1+1)+(3 : Int))=true := by
    change (machine.system.run 2133586).tape 3=true
    exact one_3
  obtain ⟨n,e,hn,he,hseg⟩ := dispatch261_zero_to83 3 (-2) t h0 h1 h2 hm
  have hcfg : machine.system.run 2133586 = cfg 261 (-2) t := by
    have hstate := state261
    have hhead := head_neg2
    cases hc : machine.system.run 2133586 with
    | mk state head tape =>
      simp only [hc,cfg] at hstate hhead ⊢
      simp only [t,hc,cfg] at *
      cases hstate
      cases hhead
      rfl
  refine ⟨n,e,hn,he,?_⟩
  apply segAdd machine _ _ _ 2133586 n blank_start_66
  rw [← run_2133586, hcfg]
  exact hseg

end Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch

#print axioms Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch.blank_start_second_dispatch_to83
