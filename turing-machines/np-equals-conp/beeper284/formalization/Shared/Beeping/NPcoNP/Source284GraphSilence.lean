import Shared.Beeping.NPcoNP.Source284GraphControllerRefinement
import Shared.Beeping.WordEventCoverage

/-! Source-specific eventual-silence characterization for the pinned
register graph. No physical-table or complexity-class bridge is asserted. -/
namespace Shared.Beeping.NPcoNP.Source284GraphSilence
open PASoundness Shared.Beeping
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphControllerRefinement

theorem source_erase : source.erase = Controller.system Source284Comparison.compare 0 := by
  apply eventSystem_ext
  · rfl
  · funext s
    change (((Controller.system Source284Comparison.compare 0).step s).1,
      !((if ((Controller.system Source284Comparison.compare 0).step s).2 then [()] else []).map
        (fun _ => true)).isEmpty) = (Controller.system Source284Comparison.compare 0).step s
    cases h : (Controller.system Source284Comparison.compare 0).step s with
    | mk t event => cases event <;> simp [h]

/-- The coalesced producer graph is eventually silent exactly when some
source-specific candidate disagrees with the reference on every input. -/
theorem eventuallySilent_iff : target.system.erase.EventuallySilent ↔
    ∃ j, ∀ i, Source284Comparison.candidate j i = !Source284Comparison.reference i := by
  have h := WordEventCoverage.eventuallySilent_iff simulation rfl
  rw [source_erase,Source284Comparison.controller_silent_iff] at h
  exact h.symm

theorem infinitelyManyBeeps_iff :
    target.system.erase.InfinitelyManyBeeps ↔
      ¬ ∃ j, ∀ i, Source284Comparison.candidate j i = !Source284Comparison.reference i := by
  rw [← EventSystem.not_eventuallySilent_iff_infinitelyMany,eventuallySilent_iff]

end Shared.Beeping.NPcoNP.Source284GraphSilence
