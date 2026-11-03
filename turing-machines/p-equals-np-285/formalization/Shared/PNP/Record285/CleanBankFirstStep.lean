import Shared.PNP.Record285.CleanBankStep

/-! The first real post-initialization instruction satisfies the common
clean-bank action interface. Later readiness is a separate obligation. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option exponentiation.threshold 8192

namespace Shared.PNP.Record285.CleanBank
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementShift (suffixBits)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.InitializationComposition

def initialBefore : List Nat := List.replicate 6 0
def initialAfter : List Nat := List.replicate 1902 0

theorem initial_fields : initialBefore++[0]++initialAfter = List.replicate 1909 0 := by decide

theorem initial_bank :
    IncrementSelector.blocksBits (initialBefore++[0]) (suffixBits initialAfter 0) =
      IncrementSelector.blocksBits (List.replicate 1909 0) 0 := by
  rw [suffix_blank,← IncrementMeaning.blocks_append,initial_fields]

theorem initial_increment_path : walk rootIndex [false] = some (.inc 6) := by decide

/-- The concrete initialized root has the exact clean-zero increment layout
for physical field six, including all 1,909 initial bank fields. -/
theorem initial_increment_layout :
    Rel (denote (rightWord treeRoot (-1) [false] false rootLeft []) (-3817) 0
      (2*runPattern false 3818 true
        (2*IncrementSelector.blocksBits (initialBefore++[0]) (suffixBits initialAfter 0))))
      (Record285.machine.system.run 89806142) := by
  have h := InitializationComplete.blank_start_entry.1
  rw [candidate_clean_numeric] at h
  rw [initial_bank]
  have he : denote (rightWord treeRoot (-1) [false] false rootLeft []) (-3817) 0
      (2*runPattern false 3818 true
        (2*IncrementSelector.blocksBits (List.replicate 1909 0) 0)) =
      denote (rightWord treeRoot 0 [] false rootLeft [false]) (-3818) 0
        (runPattern false 3819 true
          (2*IncrementSelector.blocksBits (List.replicate 1909 0) 0)) := by
    simp [rightWord,denote,bits,runPattern,bitVal]
  rw [he]
  exact h

/-- The first root dispatch is the actual increment of field six. -/
theorem initial_ready :
    Ready (.inc 6) (List.replicate 1909 0) (Record285.machine.system.run 89806142) := by
  rw [← initial_fields]
  have hp : walk rootIndex [false] = some (.inc initialBefore.length) := by
    simpa [initialBefore] using initial_increment_path
  exact Ready.inc 3818 0 initialBefore initialAfter [false] false (-3817) 0
    (2*runPattern false 3818 true
      (2*IncrementSelector.blocksBits (initialBefore++[0]) (suffixBits initialAfter 0))) _ hp rfl
    initial_increment_layout

/-- This first increment returns to a clean root with field six equal to one
and every other recorded field zero. No event occurs during the segment. -/
theorem first_increment_returns_clean_root :
    ∃ steps, 0 < steps ∧
      Root (initialBefore++[1]++initialAfter)
        ((Shared.Beeping.EventSystem.mk (Record285.machine.system.run 89806142) Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬
        (Shared.Beeping.EventSystem.mk (Record285.machine.system.run 89806142) Record285.machine.step).BeepAt t := by
  have hp : walk rootIndex [false] = some (.inc initialBefore.length) := by
    simpa [initialBefore] using initial_increment_path
  simpa only [Nat.zero_add] using increment_preserves 3818 0 initialBefore initialAfter [false] hp false
    (-3817) 0 (2*runPattern false 3818 true
      (2*IncrementSelector.blocksBits (initialBefore++[0]) (suffixBits initialAfter 0)))
    rfl _ initial_increment_layout

/-- The exact first increment return is already in the layout for the next
beep instruction. The complete bank and both outer tails are unchanged by
this representation equality. -/
theorem first_return_is_beep_layout (bank : Nat) :
    denote (rightWord treeRoot 0 [] true rootLeft [false]) (-3818) 0
      (runPattern false 3819 true (2*bank)) =
    denote (rightWord treeRoot (-3) beepCode false rootLeft []) (-3815) 0
      (2*runPattern false 3816 true (2*bank)) := by
  have hz : runPattern false 3819 true (2*bank) =
      2*(2*(2*runPattern false 3816 true (2*bank))) := by
    rw [show 3819 = 3816+1+1+1 by omega]
    simp only [runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
  rw [hz]
  simp [rightWord,denote,bits,beepCode,bitVal]

/-- Starting at the verified blank-start root, the first increment is
silent, then the next instruction beeps exactly once and returns to the
same clean bank. This is still only a finite prefix of the machine run. -/
theorem first_increment_then_beep :
    let start := Record285.machine.system.run 89806142
    let fields := initialBefore++[1]++initialAfter
    ∃ firstSteps, 0 < firstSteps ∧
      (∀ t, t < firstSteps → ¬ (Shared.Beeping.EventSystem.mk start Record285.machine.step).BeepAt t) ∧
      let middle := (Shared.Beeping.EventSystem.mk start Record285.machine.step).run firstSteps
      let secondSteps := beepDuration false 3816
      Root fields ((Shared.Beeping.EventSystem.mk middle Record285.machine.step).run secondSteps) ∧
      (∀ t, t < secondSteps →
        ((Shared.Beeping.EventSystem.mk middle Record285.machine.step).BeepAt t ↔
          t = beepEventTime false 3816)) ∧ 0 < secondSteps := by
  dsimp only
  let start := Record285.machine.system.run 89806142
  let updated := IncrementSelector.blocksBits (initialBefore++[1])
    (IncrementSelector.blocksBits initialAfter 0)
  have hp : walk rootIndex [false] = some (.inc initialBefore.length) := by
    simpa [initialBefore] using initial_increment_path
  obtain ⟨steps,hpos,_,hroot,hquiet⟩ := PreparedIncrement.root_increment_both_markers
    3818 0 initialBefore initialAfter [false] hp false (-3817) 0
    (2*runPattern false 3818 true
      (2*IncrementSelector.blocksBits (initialBefore++[0]) (suffixBits initialAfter 0)))
    0 rfl start initial_increment_layout
  change Rel (denote (rightWord treeRoot 0 [] true rootLeft [false]) (-3818) 0
      (runPattern false 3819 true (2*updated)))
      ((Shared.Beeping.EventSystem.mk start Record285.machine.step).run steps) at hroot
  have hrepr := first_return_is_beep_layout updated
  have hmid : Rel (denote (rightWord treeRoot (-3) beepCode false rootLeft []) (-3815) 0
      (2*runPattern false 3816 true (2*updated)))
      ((Shared.Beeping.EventSystem.mk start Record285.machine.step).run steps) := by
    rw [← hrepr]
    exact hroot
  have hb := beep_preserves 3816 (initialBefore++[1]++initialAfter) beepCode beep_path false
    (-3815) 0 (2*runPattern false 3816 true (2*updated))
    (by simp only [Bool.false_eq_true,if_false,updated,IncrementMeaning.blocks_append])
    ((Shared.Beeping.EventSystem.mk start Record285.machine.step).run steps) hmid
  exact ⟨steps,hpos,hquiet,hb.2.1,hb.2.2,hb.1⟩

end Shared.PNP.Record285.CleanBank
