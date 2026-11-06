import Shared.Beeping.NPcoNP.Grammar284ActiveRun
import Shared.Beeping.NPcoNP.Source284GraphTableConditional
import Shared.Beeping.WordUnboundedPrefix

/-! The whole literal equivalence follows from one reachable, word-aligned active
window. Reachability of that window is an explicit outstanding obligation. -/
namespace Shared.Beeping.NPcoNP.Grammar284ActiveEndpoint
open ComplexityTheory PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.Grammar284ActiveWindow
open Shared.Beeping.NPcoNP.Grammar284ActiveRun
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphTableConditional
open Shared.Beeping.NPcoNP.Source284AllInputReferenceCoverage
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

/-- A literal parser boundary reachable with precisely the same event prefix as
a graph run. This proposition is not asserted to hold. -/
def AlignedActiveWindow : Prop :=
  ∃ (graphTime physicalTime : Nat) (origin separator : Int) (t : Int → Bool),
    physical.run physicalTime=cfg 93 (origin+1) t ∧
    physical.prefixWord physicalTime=target.system.prefixWord graphTime ∧
    ActiveWindow (target.system.run graphTime).state (target.system.run graphTime).bank origin separator t

theorem cofinal_of_aligned (h : AlignedActiveWindow) :
    WordUnboundedPrefix.CofinalPairMatch target.system physical := by
  obtain ⟨g,p,origin,separator,t,hrun,hword,hwindow⟩ := h
  intro n
  obtain ⟨k,out,hk,_,_,hmatch⟩ := prefix_runs n (target.system.run g) origin separator t hwindow
  refine ⟨g+n,p+k,by omega,by omega,?_⟩
  rw [WordEventSystem.prefix_add,hrun,hword,hmatch,WordEventSystem.prefix_add]

/-- Conditional endpoint: it remains to establish a word-aligned active window
for the literal blank-start run. -/
theorem selected_table_silent_iff_classes_of_aligned (h : AlignedActiveWindow) :
    machine.system.EventuallySilent ↔ NP = coNP := by
  have hs := WordUnboundedPrefix.eventuallySilent_iff_of_cofinalPairs target.system physical (cofinal_of_aligned h)
  rw [fromFlags_erase] at hs
  exact hs.symm.trans graph_eventuallySilent_iff_classes

#print axioms selected_table_silent_iff_classes_of_aligned
end Shared.Beeping.NPcoNP.Grammar284ActiveEndpoint
