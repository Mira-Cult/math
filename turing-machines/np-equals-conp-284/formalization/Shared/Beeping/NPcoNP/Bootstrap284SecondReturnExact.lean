import Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch
import Shared.Beeping.NPcoNP.NativeHalfDispatchSelector

/-! Strengthen the checked second physical return with the exact full tape
effect. This is a finite blank-start segment, not an all-run simulation. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284SecondReturnExact

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfDispatchSelector
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch

set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

theorem zero_1 : (machine.system.run 2133586).tape 1=false := by
  rw [run_2133586]
  decide

theorem zero_2 : (machine.system.run 2133586).tape 2=false := by
  rw [run_2133586]
  decide

/-- From blank tape, the second checked zero-dispatch reaches state 93 with
the exact tape produced by setting cell -2 and filling cells 0, 1 and 2. -/
theorem blank_start_second_return_exact :
    ∃ (n : Nat) (e : Config 284), 7<n ∧ e.state=93 ∧
      e.tape=fillRange (setAt (-2) (machine.system.run 2133586).tape) 0 3 ∧
      silentSegment machine (machine.system.run 0) e (2133586+n) := by
  let t := (machine.system.run 2133586).tape
  have hz : ∀ i : Nat, i<3 → t ((-2)+2+(i : Int))=false := by
    intro i hi
    have hi' : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi' with rfl | rfl | rfl
    · exact zero_0
    · exact zero_1
    · exact zero_2
  obtain ⟨z,htail⟩ := run_has_left_zero 2133586
  have hx : Holds t (-2) [] := trivial
  have hd : (-2 : Int)+([] : List Bool).length≤(-2) ∨ (-2)+2+(3 : Int)≤(-2) := by simp
  have h1 : t ((-2)+1)=false := by
    change (machine.system.run 2133586).tape (-1)=false
    exact zero_neg1
  have hm : t ((-2)+2+(3 : Int))=true := by
    change (machine.system.run 2133586).tape 3=true
    exact one_3
  obtain ⟨n,e,hn,he,ht,_,hseg⟩ :=
    dispatch_zero_through_selector 3 (-2) z (-2) t [] (by decide)
      zero_neg2 h1 hz hm htail hx hd
  have hc : machine.system.run 2133586=cfg 261 (-2) t := by
    have hs := state261
    have hh := head_neg2
    cases hrun : machine.system.run 2133586 with
    | mk state head tape =>
      simp only [hrun,cfg] at hs hh ⊢
      simp only [t,hrun,cfg] at *
      cases hs
      cases hh
      rfl
  refine ⟨n,e,hn,he,?_,?_⟩
  · change e.tape=fillRange (setAt (-2) t) 0 3
    exact ht
  · apply segAdd machine _ _ _ 2133586 n blank_start_66
    rw [← run_2133586,hc]
    exact hseg

end Shared.Beeping.NPcoNP.Bootstrap284SecondReturnExact

#print axioms Shared.Beeping.NPcoNP.Bootstrap284SecondReturnExact.blank_start_second_return_exact
