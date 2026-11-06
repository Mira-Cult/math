import Shared.Beeping.NPcoNP.Parent290MaskData

/-! Local facts about the generated retained-register program and masks.
The source-grammar and physical-table bindings remain unproved. -/
namespace Shared.Beeping.NPcoNP.Parent290MaskData
open Shared.Beeping.NPcoNP.AbstractMasks
open Shared.Beeping.NPcoNP.MaskInvariant

theorem initial_covers : Covers (masks program.start) (fun _ => 0) := by
  intro q
  unfold admits
  fin_cases q <;> decide

theorem half70_work_image : image program.code[70].action true (masks 70) 6 ⊆ {Category.zero} := by decide
theorem half70_peer_image : image program.code[70].action true (masks 70) 9 ⊆ {Category.zero} := by decide
theorem half161_work_image : image program.code[161].action true (masks 161) 6 ⊆ {Category.zero} := by decide
theorem half161_peer_image : image program.code[161].action true (masks 161) 9 ⊆ {Category.zero} := by decide

end Shared.Beeping.NPcoNP.Parent290MaskData
