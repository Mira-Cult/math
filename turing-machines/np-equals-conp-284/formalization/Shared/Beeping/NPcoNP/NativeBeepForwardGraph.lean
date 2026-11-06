import Shared.Beeping.NPcoNP.NativeBeepForwardControl
import Shared.Beeping.NPcoNP.Bootstrap284ObservedGrammar
import Shared.Beeping.NPcoNP.Source284GraphBoot

/-! Bind the full ascending path observed in the finite first-beep control
to its indexed producer-grammar row and retained graph instruction. The
operational graph/tape relation and blank-start beep reachability remain open. -/
namespace Shared.Beeping.NPcoNP.NativeBeepForwardGraph
open PASoundness PASoundness.RegisterMachine Shared.Beeping
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.GrammarFullRowsCoverage
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Bootstrap284ObservedGrammar
open Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepForwardControl
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

def firstDecrementPath : List Bool := [true,true,false,true,false,false]

theorem first_decrement_leaf :
    traceState557.acc.leaves[1]? = some (firstDecrementPath,"3.$coalesced.4.decnz") := by decide

theorem first_decrement_full_row :
    fullRow traceState557.acc.starts (firstDecrementPath,"3.$coalesced.4.decnz") =
      some ⟨"3.$coalesced.4.decnz",[2,3]⟩ := by
  have hleaf : 1<traceState557.acc.leaves.size := by rw [producerLeafCount]; decide
  have hc := allRows 1 hleaf
  have hr : producerFullRows[1]? = some ⟨"3.$coalesced.4.decnz",[2,3]⟩ := by decide
  simp only [indexedRowCheck,first_decrement_leaf,hr,beq_iff_eq] at hc
  exact hc

theorem first_decrement_retained : producerNumbering.map[1]? = some (some 1) := by decide

/-- The complete word picks out the first retained decrement occurrence;
an operation name alone would not distinguish repeated occurrences. -/
theorem first_path_graph_data :
    traceState557.acc.leaves[1]? = some (firstDecrementPath,"3.$coalesced.4.decnz") ∧
    producerNumbering.map[1]? = some (some 1) ∧
    (let ins := target.code[1]
     ins.action = .base (.decNZ 4) ∧ ins.yes=1 ∧ ins.no=2) :=
  ⟨first_decrement_leaf,first_decrement_retained,contracted_pc1_instruction⟩

/-- In the checked graph the initial beep's next instruction is row 1. -/
theorem graph_initial_beep_targets_first_decrement :
    (target.system.step target.system.initial).2=[true] ∧
      (target.system.step target.system.initial).1.state=1 := by
  constructor <;> decide

/-- Under the explicit finite local layout, a reachable physical beep and
return yield the complete first-decrement path, one event, and the same
next action as the checked graph's initial beep. Bank correspondence and
all subsequent graph steps remain separate obligations. -/
theorem reachable_return_matches_first_path (time : Nat) (hb : machine.system.BeepAt time)
    (hm1 : (machine.system.run time).tape ((machine.system.run time).head-1)=false)
    (hm2 : (machine.system.run time).tape ((machine.system.run time).head-2)=false)
    (hm3 : (machine.system.run time).tape ((machine.system.run time).head-3)=true)
    (hm4 : (machine.system.run time).tape ((machine.system.run time).head-4)=true)
    (hp1 : (machine.system.run time).tape ((machine.system.run time).head+1)=false)
    (p : Int) (hp : (machine.system.run time).head<p)
    (hone : (machine.system.run time).tape p=true) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      Holds out ((machine.system.run time).head-4) firstDecrementPath ∧
      parseForward 52 out ((machine.system.run time).head-4)=
        some ("3.$coalesced.4.decnz",6) ∧
      machine.system.run (time+n)=cfg 83 ((machine.system.run time).head-2) out ∧
      physical.wordFrom (machine.system.run time) n=[true] ∧
      (target.system.step target.system.initial).2=[true] ∧
      (target.system.step target.system.initial).1.state=1 ∧
      producerNumbering.map[1]?=some (some 1) := by
  obtain ⟨n,out,hn,hword,hparse,hrun,hevent⟩ :=
    reachable_beep_returns_forward_decrement time hb hm1 hm2 hm3 hm4 hp1 p hp hone
  exact ⟨n,out,hn,hword,hparse,hrun,hevent,graph_initial_beep_targets_first_decrement.1,
    graph_initial_beep_targets_first_decrement.2,first_decrement_retained⟩

#print axioms first_decrement_leaf
#print axioms first_decrement_full_row
#print axioms first_path_graph_data
#print axioms graph_initial_beep_targets_first_decrement
#print axioms reachable_return_matches_first_path
end Shared.Beeping.NPcoNP.NativeBeepForwardGraph
