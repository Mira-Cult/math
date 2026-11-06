import Shared.Beeping.NPcoNP.Source284GraphBoot
import Shared.Beeping.NPcoNP.Source284GraphInputCopy
import Shared.Beeping.NPcoNP.Source284GraphParserComplete
import Shared.Beeping.NPcoNP.Source284GraphBranchCopy

/-! End-to-end graph-level setup for the reference phase. A supplied PC 2
configuration contains the candidate input in register 4. The proof copies
that input, runs the marker/payload parser, and initializes the descending
certificate counter. It does not establish physical-tape execution or
correctness of the subsequent bounded evaluator. -/

namespace Shared.Beeping.NPcoNP.Source284GraphReferenceSetup
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284Parser
open Shared.Beeping.NPcoNP.Source284GraphParserTotal

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

abbrev Bank := PASoundness.RegisterMachine.Bank 12

def parsedBank (b : Bank) : Bank :=
  header (write b 0 (b 4)) 0 (length (b 4)) (description (b 4))

def readyBank (b : Bank) : Bank :=
  write (parsedBank b) 7 (description (b 4))

@[simp] theorem parsed_scratch9 (b : Bank) (h : b 9 = 0) : parsedBank b 9 = 0 := by
  simp [parsedBank, header, write, h]

@[simp] theorem parsed_scratch10 (b : Bank) (h : b 10 = 0) : parsedBank b 10 = 0 := by
  simp [parsedBank, header, write, h]

@[simp] theorem parsed_description (b : Bank) :
    parsedBank b 6 = description (b 4) := by
  simp [parsedBank, header, write]

@[simp] theorem ready_input (b : Bank) : readyBank b 4 = b 4 := by
  simp [readyBank, parsedBank, header, write]

theorem reference_setup (b : Bank) (h9 : b 9 = 0) (h10 : b 10 = 0) :
    ∃ k, 0 < k ∧ target.system.advance ⟨2,b⟩ k = ⟨31,readyBank b⟩ ∧
      target.system.wordFrom ⟨2,b⟩ k = [] := by
  let c := write b 0 (b 4)
  let q := 7 * b 4 + b 0 + 4
  have hi := Shared.Beeping.NPcoNP.Source284GraphInputCopy.input_copy b h9 h10
  have hiSegment : SilentSegment ⟨2,b⟩ ⟨10,c⟩ q := ⟨hi.1, hi.2.1⟩
  have hc10 : c 10 = 0 := by simp [c, write, h10]
  obtain ⟨l, hl, hp, hw⟩ :=
    Shared.Beeping.NPcoNP.Source284GraphParserComplete.parser_from_pc10 c hc10
  change target.system.advance ⟨10,c⟩ l =
    ⟨23,header c 0 (length (c 0)) (description (c 0))⟩ at hp
  have hc0 : c 0 = b 4 := rfl
  rw [hc0] at hp
  have hp' : target.system.advance ⟨10,c⟩ l = ⟨23,parsedBank b⟩ := hp
  have hw' : target.system.wordFrom ⟨10,c⟩ l = [] := by
    exact hw
  have hpSegment : SilentSegment ⟨10,c⟩ ⟨23,parsedBank b⟩ l := ⟨hp', hw'⟩
  have hb := Shared.Beeping.NPcoNP.Source284GraphBranchCopy.branch_copy
    (parsedBank b) (parsed_scratch9 b h9) (parsed_scratch10 b h10)
  let r := 7 * (parsedBank b) 6 + (parsedBank b) 7 + 4
  have hbAdvance : target.system.advance ⟨23,parsedBank b⟩ r = ⟨31,readyBank b⟩ := by
    change target.system.advance ⟨23,parsedBank b⟩ r =
      ⟨31,write (parsedBank b) 7 (description (b 4))⟩
    rw [← parsed_description b]
    exact hb.1
  have hbSegment : SilentSegment ⟨23,parsedBank b⟩ ⟨31,readyBank b⟩ r :=
    ⟨hbAdvance, hb.2.1⟩
  have total := cat (cat hiSegment hpSegment) hbSegment
  exact ⟨q + l + r, by dsimp [q]; omega, total.1, total.2⟩

/-- Starting from the graph's all-zero initial bank, the reference setup is
reached after the explicit startup beep and finitely many silent steps. -/
theorem initial_reference_setup :
    ∃ k, 2 < k ∧ target.system.run k = ⟨31,readyBank (fun _ => 0)⟩ ∧
      target.system.prefixWord k = [true] := by
  obtain ⟨k, hk, ha, hw⟩ := reference_setup (fun _ => 0) rfl rfl
  refine ⟨2+k, by omega, ?_, ?_⟩
  · rw [WordEventSystem.run_add, Source284GraphBoot.startup_config, ha]
  · rw [WordEventSystem.prefix_add, Source284GraphBoot.startup_config,
      Source284GraphBoot.startup_word, hw]
    rfl

end Shared.Beeping.NPcoNP.Source284GraphReferenceSetup
