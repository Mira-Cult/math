import Shared.PNP.Record285.GrammarBeepUnique
import Shared.Beeping.Refinement

/-! Complete physical beep dispatch, marked event, cleanup, and root return
for the explicitly described finite-support tape layout. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Grammar
open Shared.Beeping
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
attribute [local irreducible] Record285.machine

theorem advance_eq_restarted_run {C : Type} (sys : EventSystem C) (start : C) (t : Nat) :
    sys.advance start t = (EventSystem.mk start sys.step).run t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [EventSystem.advance,EventSystem.run_succ,ih]

theorem restarted_run_offset {C : Type} (sys : EventSystem C) (start t : Nat) :
    (EventSystem.mk (sys.run start) sys.step).run t = sys.run (start+t) := by
  rw [EventSystem.run_add,advance_eq_restarted_run]

theorem restarted_beep_offset {C : Type} (sys : EventSystem C) (start t : Nat) :
    (EventSystem.mk (sys.run start) sys.step).BeepAt t ↔ sys.BeepAt (start+t) := by
  simpa only [EventSystem.BeepFrom,advance_eq_restarted_run,EventSystem.BeepAt] using
    (EventSystem.beepAt_add_iff sys start t).symm

def beepCode : List Bool := [true,false,false]
def beepPrecode : List Bool := [true,false]

theorem beep_path : walk rootIndex beepCode = some .beep := by
  simp [beepCode,rootIndex,walk,root_true_edge,next_false_edge,beep_false_edge]

theorem beep_prefix_safe : detectorRun 0 (scanWord beepPrecode) = some 0 := by decide

theorem beep_return_rule : returnPath beepCode = some (beepPrecode ++ [true]) := by decide

/-- Dispatch through the single marked event and return to state 284. The
only event in the segment is at time 3. The following bank and both distant
tails are represented exactly; source reachability is not assumed or proved. -/
theorem beep_returns_root_physical (gap : Nat) (head : Int) (leftTail tail : Nat)
    (physical : Machines.Config 285)
    (hrel : Rel (markedRootEntry beepCode head leftTail
      (2*runPattern true (gap+1) false tail)) physical) :
    let steps := 2*gap+32
    let sys := EventSystem.mk physical Record285.machine.step
    Rel (denote (rightWord treeRoot (-2) beepPrecode true rootLeft [false])
      (head-1) leftTail (runPattern false (gap+1) true (2*tail))) (sys.run steps) ∧
    (∀ t, t < steps → (sys.BeepAt t ↔ t = 3)) ∧ 0 < steps := by
  dsimp only
  let sys := EventSystem.mk physical Record285.machine.step
  let far := bits (pathLeft beepPrecode) leftTail
  let bank := runPattern true (gap+1) false tail
  have hb := root_beep_physical beepCode beep_path head leftTail (2*bank) physical hrel
  have hword : bits (beepCode.reverse++rootLeft) leftTail = runPattern true 0 false far := by
    simp [beepCode,beepPrecode,pathLeft,rootLeft,bits,runPattern,bitVal,far]
  have hconfig :
      (⟨⟨1,by decide⟩,head-1,
        bits (beepCode.reverse++rootLeft) leftTail/2,
        (bits (beepCode.reverse++rootLeft) leftTail).testBit 0,2*(2*bank)⟩ : PhysicalNumeric.Config 285) =
      atLeftWord IncrementCleanup.lexical (head-1) (runPattern true 0 false far) (4*bank) := by
    have hh : 2*(2*bank) = 4*bank := by omega
    rw [hword,hh]
    rfl
  have hpost : Rel (atLeftWord IncrementCleanup.lexical (head-1)
      (runPattern true 0 false far) (4*bank)) (sys.run 4) := by
    have h := hb.2.2
    change Rel _ (sys.run 4) at h
    rw [hconfig] at h
    exact h
  let cleanupSteps := 2*gap+9
  have hc := IncrementCleanup.literal_cleanup_physical 0 gap head far tail (sys.run 4) hpost
  simp only [Nat.mul_zero,Nat.zero_add,Int.natCast_zero,Int.sub_zero] at hc
  let returnTail := runPattern false (gap+1) true (2*tail)
  have hright : 1+2*runPattern false (gap+2) true (2*tail) = 1+4*returnTail := by
    dsimp only [returnTail]
    rw [show gap+2 = (gap+1)+1 by omega,runPattern]
    simp only [bitVal,Bool.false_eq_true,if_false]
    omega
  rw [hright] at hc
  have hr := literal_return_root beepPrecode beep_prefix_safe (head-1) leftTail returnTail
  have hpos : (head-1)-1 = head-2 := by omega
  rw [hpos] at hr
  change silent Record285.machine 19
    (atLeftWord IncrementPreparation.dispatch0 (head-2) far (1+4*returnTail)) = _ at hr
  have hp := silent_physical Record285.machine _
    ((EventSystem.mk (sys.run 4) sys.step).run cleanupSteps) hc.1 19 _ hr
  have hoff : (EventSystem.mk (sys.run 4) sys.step).run cleanupSteps = sys.run (4+cleanupSteps) :=
    restarted_run_offset sys 4 cleanupSteps
  have hoff' : (EventSystem.mk (sys.run (4+cleanupSteps)) sys.step).run 19 =
      sys.run (4+cleanupSteps+19) := restarted_run_offset sys (4+cleanupSteps) 19
  rw [hoff] at hp
  rw [hoff'] at hp
  have htime : 4+cleanupSteps+19 = 2*gap+32 := by dsimp [cleanupSteps]; omega
  rw [htime] at hp
  refine ⟨?_,?_,by omega⟩
  · exact hp.1
  · intro t ht
    constructor
    · intro he
      by_cases hbefore : t < 3
      · exact False.elim ((hb.1 t hbefore) he)
      by_cases hthree : t = 3
      · exact hthree
      by_cases hclean : t < 4+cleanupSteps
      · have hquiet := hc.2 (t-4) (by omega)
        apply False.elim
        apply hquiet
        apply (restarted_beep_offset sys 4 (t-4)).2
        simpa only [show 4+(t-4)=t by omega] using he
      · have hquiet := hp.2 (t-(4+cleanupSteps)) (by omega)
        apply False.elim
        apply hquiet
        apply (restarted_beep_offset sys (4+cleanupSteps) (t-(4+cleanupSteps))).2
        simpa only [show 4+cleanupSteps+(t-(4+cleanupSteps))=t by omega] using he
    · intro ht3
      subst t
      exact hb.2.1

/-- Every producer-grammar beep path is the proved one-event root-to-root
segment. The byte binding is included; the physical start layout remains an
explicit premise. -/
theorem bound_any_beep_returns_root_physical (code : List Bool)
    (hwalk : walk rootIndex code = some .beep) (gap : Nat) (head : Int)
    (leftTail tail : Nat) (physical : Machines.Config 285)
    (hrel : Rel (markedRootEntry code head leftTail
      (2*runPattern true (gap+1) false tail)) physical) :
    literal = String.ofList (headerChars ++ renderEntries entries ++ renderedSuffix) ∧
    returnPath code = some (beepPrecode ++ [true]) ∧
    let steps := 2*gap+32
    let sys := EventSystem.mk physical Record285.machine.step
    Rel (denote (rightWord treeRoot (-2) beepPrecode true rootLeft [false])
      (head-1) leftTail (runPattern false (gap+1) true (2*tail))) (sys.run steps) ∧
    (∀ t, t < steps → (sys.BeepAt t ↔ t = 3)) ∧ 0 < steps := by
  have hw := root_beep_word code hwalk
  change code = beepCode at hw
  subst code
  exact ⟨literal_typed_serialization,beep_return_rule,
    beep_returns_root_physical gap head leftTail tail physical hrel⟩

end Shared.PNP.Record285.Grammar
