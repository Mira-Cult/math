import Shared.PNP.Record285.ControlContinueCore

/-! Connect a non-preserving grammar leaf to its exact literal control state. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ControlContinue
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar

theorem left_leaf_denote (q : Fin 285) (pre : List Bool) (head : Int) (leftTail rightTail : Nat) :
    denote (leafDestination ⟨false,.left,q,false⟩ pre) head leftTail rightTail =
      atLeftWord q (head-2) (bits (pre.reverse++rootLeft) leftTail) (4*rightTail) := by
  have hn : pre.reverse++rootLeft ≠ [] := by simp [rootLeft]
  cases h : pre.reverse++rootLeft with
  | nil => contradiction
  | cons b bs =>
    simp only [leafDestination,h,List.tail_cons,List.headD_cons,denote,atLeftWord,bits_read,bits_drop]
    simp only [bits,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
    have hh : head + -2 = head-2 := by omega
    have hr : 2*(2*rightTail) = 4*rightTail := by omega
    simp only [hh,hr]

/-- The final grammar row clears its `1` and moves left into the supplied
literal control state, preserving all remaining cells and emitting no event. -/
theorem literal_control_leaf (code pre : List Bool) (e : Edge) (q : Fin 285)
    (hwalk : walk rootIndex code = some e) (hcode : code = pre++[true])
    (hzero : expected e false = none)
    (hone : expected e true = some ⟨false,.left,q,false⟩)
    (head : Int) (leftTail rightTail : Nat) :
    silent Record285.machine code.length (rootEntry code head leftTail rightTail) =
      some (atLeftWord q (head-2) (bits (pre.reverse++rootLeft) leftTail) (4*rightTail)) := by
  obtain ⟨pre',bit,row,hcode',hexpected,hs⟩ := root_leaf_symbolic code e hwalk
  cases bit with
  | false => rw [hzero] at hexpected; contradiction
  | true =>
    rw [hone] at hexpected
    have hr : row = ⟨false,.left,q,false⟩ := Option.some.inj hexpected.symm
    subst row
    have hp : pre' = pre := List.append_cancel_right (hcode'.symm.trans hcode)
    subst pre'
    have hn := run_sound code.length _ _ hs head leftTail rightTail
    simpa only [rootEntry,left_leaf_denote] using hn

theorem left_leaf_denote_any (q : Fin 285) (pre : List Bool) (marker : Bool)
    (head : Int) (leftTail rightTail : Nat) :
    denote (leafDestinationAny ⟨false,.left,q,false⟩ pre marker) head leftTail rightTail =
      atLeftWord q (head-2) (bits (pre.reverse++rootLeft) leftTail)
        (2*(bitVal marker+2*rightTail)) := by
  have hn : pre.reverse++rootLeft ≠ [] := by simp [rootLeft]
  cases h : pre.reverse++rootLeft with
  | nil => contradiction
  | cons b bs =>
    simp only [leafDestinationAny,h,List.tail_cons,List.headD_cons,denote,atLeftWord,bits_read,bits_drop]
    simp only [bits,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
    have hh : head + -2 = head-2 := by omega
    simp only [hh]

theorem literal_control_leaf_any (code pre : List Bool) (e : Edge) (q : Fin 285)
    (hwalk : walk rootIndex code = some e) (hcode : code = pre++[true])
    (hzero : expected e false = none)
    (hone : expected e true = some ⟨false,.left,q,false⟩)
    (marker : Bool) (head : Int) (leftTail rightTail : Nat) :
    silent Record285.machine code.length
      (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft []) head leftTail rightTail) =
      some (atLeftWord q (head-2) (bits (pre.reverse++rootLeft) leftTail)
        (2*(bitVal marker+2*rightTail))) := by
  obtain ⟨pre',bit,row,hcode',hexpected,hs⟩ := root_leaf_symbolic_any code marker e hwalk
  cases bit with
  | false => rw [hzero] at hexpected; contradiction
  | true =>
    rw [hone] at hexpected
    have hr : row = ⟨false,.left,q,false⟩ := Option.some.inj hexpected.symm
    subst row
    have hp : pre' = pre := List.append_cancel_right (hcode'.symm.trans hcode)
    subst pre'
    have hn := run_sound code.length _ _ hs head leftTail rightTail
    simpa only [left_leaf_denote_any] using hn

end Shared.PNP.Record285.ControlContinue
