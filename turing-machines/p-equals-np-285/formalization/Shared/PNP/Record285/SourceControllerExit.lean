import Shared.PNP.Record285.SourceComparisonDispatch

/-! Radix rollover and candidate advance on the exact pre-control graph. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SourceControllerExit
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin
open Shared.PNP.Record285.SourceReferenceStart
open Shared.PNP.Record285.SourceReferenceBranch
open Shared.PNP.Record285.SourceReferenceSearch
open Shared.PNP.Record285.SourceUnarySkip
open Shared.PNP.Record285.SourceVirtualAction
open Shared.PNP.Record285.SourceVirtualStep
open Shared.PNP.Record285.SourceComparisonDispatch

def rolloverRaw (bank : Nat → Nat) : Nat → Nat :=
  let doubled := doubleMove 14 17 bank
  let restored := update (.move 17 14) doubled
  let incremented := update (.inc 13) restored
  let copied := splitResult 14 17 4 incremented
  let restoredAgain := update (.move 4 14) copied
  let emptied := clear 15 restoredAgain
  update (.dec 15) (update (.move 17 15) emptied)

/-- The rollover terminates silently on every finite bank, including arbitrary
scratch contents, with an exact full-bank effect. -/
theorem rollover_run (bank : Nat → Nat) :
    ∃ duration, 0 < duration ∧ Silent originalRows ⟨157,bank⟩ ⟨6,rolloverRaw bank⟩ duration := by
  let doubled := doubleMove 14 17 bank
  let restored := update (.move 17 14) doubled
  let incremented := update (.inc 13) restored
  let copied := splitResult 14 17 4 incremented
  let restoredAgain := update (.move 4 14) copied
  let emptied := clear 15 restoredAgain
  let moved := update (.move 17 15) emptied
  have hdouble := double_move_run originalRows 157 158 159 160 14 17 (bank 14) bank
    (by decide) (by decide) (by decide) (by decide) rfl
  have hrestore := expanded_move_run originalRows 160 161 162 17 14 (doubled 17) doubled
    (by decide) (by decide) (by decide) rfl
  have h162 : step originalRows ⟨162,restored⟩ = (⟨163,incremented⟩,false) := by
    simp [step,originalRows,observe,incremented]
  have hcopy := split_run originalRows 163 164 165 166 14 17 4 (incremented 14) incremented
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl
  have hrestore2 := expanded_move_run originalRows 166 167 168 4 14 (copied 4) copied
    (by decide) (by decide) (by decide) rfl
  have hclear := clear_run originalRows 168 169 15 (restoredAgain 15) restoredAgain (by decide) rfl
  have hmove := expanded_move_run originalRows 169 170 171 17 15 (emptied 17) emptied
    (by decide) (by decide) (by decide) rfl
  have h171 : step originalRows ⟨171,moved⟩ = (⟨6,update (.dec 15) moved⟩,false) := by
    simp [step,originalRows,observe]
  have h := silent_trans originalRows _ _ _ _ _ hdouble hrestore
  have h := silent_trans originalRows _ _ _ _ 1 h (silent_one _ _ _ h162)
  have h := silent_trans originalRows _ _ _ _ _ h hcopy
  have h := silent_trans originalRows _ _ _ _ _ h hrestore2
  have h := silent_trans originalRows _ _ _ _ _ h hclear
  have h := silent_trans originalRows _ _ _ _ _ h hmove
  have h := silent_trans originalRows _ _ _ _ 1 h (silent_one _ _ _ h171)
  refine ⟨(3*bank 14+1)+(2*doubled 17+1)+1+(3*incremented 14+1)+
    (2*copied 4+1)+(restoredAgain 15+1)+(2*emptied 17+1)+1,by omega,?_⟩
  simpa [rolloverRaw,moved,emptied,restoredAgain,copied,incremented,restored,doubled] using h

/-- With clean scratch, rollover has exactly the controller's radix and
remaining-input update and preserves the entire other bank. -/
theorem rollover_clean (bank : Nat → Nat) (h4 : bank 4 = 0) (h17 : bank 17 = 0) :
    rolloverRaw bank = put 13 (bank 13+1)
      (put 14 (2*bank 14) (put 15 (2*bank 14-1) bank)) := by
  funext j
  by_cases h13 : j=13
  · subst j; simp [rolloverRaw,doubleMove,splitResult,clear,put,update]
  · by_cases h14 : j=14
    · subst j; simp [rolloverRaw,doubleMove,splitResult,clear,put,update,h4,h17]
    · by_cases h15 : j=15
      · subst j; simp [rolloverRaw,doubleMove,splitResult,clear,put,update,h17]
      · by_cases h17j : j=17
        · subst j; simp [rolloverRaw,put,update,h17]
        · by_cases h4j : j=4
          · subst j; simp [rolloverRaw,clear,put,update,h4]
          · simp [rolloverRaw,doubleMove,splitResult,clear,put,update,h13,h14,h15,h17j,h4j]

def advanceBank (bank : Nat → Nat) : Nat → Nat :=
  if bank 11 = 0 then put 12 1 (put 11 (bank 12) bank)
  else put 12 (bank 12+1) (put 11 (bank 11-1) bank)

/-- Both candidate-numbering branches reach the next begin boundary in finite
silent time for every complete bank. -/
theorem advance_run (bank : Nat → Nat) :
    ∃ duration, 0 < duration ∧ Silent originalRows ⟨172,bank⟩ ⟨1,advanceBank bank⟩ duration := by
  by_cases hz : bank 11 = 0
  · have hid := dec_at_zero 11 bank hz
    have h172 : step originalRows ⟨172,bank⟩ = (⟨174,bank⟩,false) := by
      simp [step,originalRows,observe,hz,hid]
    let moved := update (.move 12 11) bank
    have hm := expanded_move_run originalRows 174 175 176 12 11 (bank 12) bank
      (by decide) (by decide) (by decide) rfl
    have h176 : step originalRows ⟨176,moved⟩ = (⟨1,update (.inc 12) moved⟩,false) := by
      simp [step,originalRows,observe]
    have heffect : update (.inc 12) moved = advanceBank bank := by
      funext j
      by_cases h12 : j=12
      · subst j; simp [advanceBank,moved,put,update,hz]
      · by_cases h11 : j=11
        · subst j; simp [advanceBank,moved,put,update,hz]
        · simp [advanceBank,moved,put,update,hz,h12,h11]
    have h := silent_trans originalRows _ _ _ 1 _ (silent_one _ _ _ h172) hm
    have h := silent_trans originalRows _ _ _ _ 1 h (silent_one _ _ _ h176)
    exact ⟨1+(2*bank 12+1)+1,by omega,by simpa [heffect] using h⟩
  · let first := update (.dec 11) bank
    have h172 : step originalRows ⟨172,bank⟩ = (⟨173,first⟩,false) := by
      simp [step,originalRows,observe,hz,first]
    have h173 : step originalRows ⟨173,first⟩ = (⟨1,update (.inc 12) first⟩,false) := by
      simp [step,originalRows,observe]
    have heffect : update (.inc 12) first = advanceBank bank := by
      funext j
      by_cases h12 : j=12
      · subst j; simp [advanceBank,first,put,update,hz]
      · by_cases h11 : j=11
        · subst j; simp [advanceBank,first,put,update,hz]
        · simp [advanceBank,first,put,update,hz,h12,h11]
    have h := silent_trans originalRows _ _ _ 1 1 (silent_one _ _ _ h172) (silent_one _ _ _ h173)
    exact ⟨2,by decide,by simpa [heffect] using h⟩

theorem advance_source (bank : Nat → Nat) :
    sourceState (advanceBank bank) .begin =
      ⟨(Source.advanceCandidate (bank 11) (bank 12)).1,
       (Source.advanceCandidate (bank 11) (bank 12)).2,bank 13,bank 14,bank 15,.begin⟩ := by
  by_cases hz : bank 11 = 0 <;> simp [sourceState,advanceBank,Source.advanceCandidate,put,hz]

/-- The maintained scratch invariant at source-controller boundaries. -/
def ControllerReady (bank : Nat → Nat) : Prop := ReferenceReady bank ∧ bank 6 = 0 ∧ bank 7 = 0

/-- One complete source comparison step, including its decision and either
rollover or candidate advance. The resulting graph boundary represents exactly
the controller successor; every intermediate graph transition is silent. -/
theorem controller_compare_step (bank : Nat → Nat) (hready : ControllerReady bank) :
    ∃ out duration, 0 < duration ∧
      Silent originalRows ⟨6,bank⟩
        ⟨if Source.mismatch (bank 11) (bank 12) (bank 13) (bank 14) (bank 15) then 1 else 6,out⟩ duration ∧
      ControllerReady out ∧
      sourceState out (if Source.mismatch (bank 11) (bank 12) (bank 13) (bank 14) (bank 15)
        then .begin else .compare) = (Source.controllerStep (sourceState bank .compare)).1 ∧
      (∀ j, 21 ≤ j → out j = bank j) := by
  obtain ⟨mid,d,hd,hmready,hmframe,hcase⟩ := comparison_and_dispatch bank hready.1 hready.2.1 hready.2.2
  have hm6 : mid 6 = 0 := by
    rw [hmframe 6 (by unfold Protected; omega) (by decide),hready.2.1]
  have hm7 : mid 7 = 0 := by
    rw [hmframe 7 (by unfold Protected; omega) (by decide),hready.2.2]
  have hm11 : mid 11 = bank 11 := hmframe 11 (by unfold Protected; omega) (by decide)
  have hm12 : mid 12 = bank 12 := hmframe 12 (by unfold Protected; omega) (by decide)
  have hm13 : mid 13 = bank 13 := hmframe 13 (by unfold Protected; omega) (by decide)
  have hm14 : mid 14 = bank 14 := hmframe 14 (by unfold Protected; omega) (by decide)
  have htail : ∀ j, 21 ≤ j → mid j = bank j := by
    intro j hj; apply hmframe j <;> simp [Protected] <;> omega
  cases hb : Source.mismatch (bank 11) (bank 12) (bank 13) (bank 14) (bank 15) with
  | true =>
    simp only [hb,if_true] at hcase
    obtain ⟨hseg,hbit,hm15⟩ := hcase
    obtain ⟨e,he,hadvance⟩ := advance_run mid
    let out := advanceBank mid
    have hout : ControllerReady out := by
      by_cases hz : mid 11=0 <;>
        simp [ControllerReady,ReferenceReady,out,advanceBank,put,hz,hmready.1,hmready.2.1,hmready.2.2,hm6,hm7]
    have hsource : sourceState out .begin = (Source.controllerStep (sourceState bank .compare)).1 := by
      rw [show sourceState out .begin = _ from advance_source mid]
      simp [Source.controllerStep,sourceState,hb,hm11,hm12,hm13,hm14,hm15]
    have houttail : ∀ j, 21 ≤ j → out j = bank j := by
      intro j hj
      have h11 : j ≠ 11 := by omega
      have h12 : j ≠ 12 := by omega
      by_cases hz : mid 11=0 <;> simp [out,advanceBank,put,hz,h11,h12,htail j hj]
    refine ⟨out,d+e,by omega,?_,hout,?_,houttail⟩
    · simpa only [if_true] using silent_trans originalRows _ _ _ _ _ hseg hadvance
    · simpa only [if_true] using hsource
  | false =>
    simp only [hb] at hcase
    by_cases hz : bank 15 = 0
    · simp only [hz,if_true] at hcase
      obtain ⟨hseg,hbit,hm15⟩ := hcase
      obtain ⟨e,he,hroll⟩ := rollover_run mid
      let out := rolloverRaw mid
      have hv := rollover_clean mid hmready.1 hmready.2.2
      have hout : ControllerReady out := by
        simp [ControllerReady,ReferenceReady,out,hv,put,hmready.1,hmready.2.1,hmready.2.2,hm6,hm7]
      have hb0 : Source.mismatch (bank 11) (bank 12) (bank 13) (bank 14) 0 = false := by simpa [hz] using hb
      have hsource : sourceState out .compare = (Source.controllerStep (sourceState bank .compare)).1 := by
        simp [sourceState,out,hv,put,Source.controllerStep,hb0,hz,hm11,hm12,hm13,hm14]
      have houttail : ∀ j, 21 ≤ j → out j = bank j := by
        intro j hj
        have h13 : j ≠ 13 := by omega
        have h14 : j ≠ 14 := by omega
        have h15 : j ≠ 15 := by omega
        simp [out,hv,put,h13,h14,h15,htail j hj]
      refine ⟨out,d+e,by omega,?_,hout,?_,houttail⟩
      · simpa only [Bool.false_eq_true,if_false] using silent_trans originalRows _ _ _ _ _ hseg hroll
      · simpa only [Bool.false_eq_true,if_false] using hsource
    · simp only [hz,if_false] at hcase
      obtain ⟨hseg,hbit,hm15⟩ := hcase
      have hout : ControllerReady mid := ⟨hmready,hm6,hm7⟩
      have h15 : mid 15 = bank 15-1 := by omega
      have hsource : sourceState mid .compare = (Source.controllerStep (sourceState bank .compare)).1 := by
        simp [sourceState,Source.controllerStep,hb,hz,hm11,hm12,hm13,hm14,h15]
      refine ⟨mid,d,hd,?_,hout,?_,htail⟩
      · simpa only [Bool.false_eq_true,if_false] using hseg
      · simpa only [Bool.false_eq_true,if_false] using hsource

end Shared.PNP.Record285.SourceControllerExit
