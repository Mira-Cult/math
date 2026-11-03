import Shared.PNP.Record285.SourceVirtualAction

/-! The live-state and HALT exits after the checked virtual tape update. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SourceVirtualFinish
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin
open Shared.PNP.Record285.SourceReferenceStart
open Shared.PNP.Record285.SourceUnarySkip
open Shared.PNP.Record285.SourceVirtualAction

def liveBank (bank : Nat → Nat) : Nat → Nat :=
  put 3 (bank 3-1+2*(bank 2%2)) (put 2 (bank 2/2) bank)

def liveTime (bank : Nat → Nat) : Nat := if bank 2%2=0 then 2 else 4

/-- Checked layout of the nonzero-state continuation. -/
structure LiveLayout (rows : Array Row) (head halt exit : Nat) : Prop where
  r0 : rows[head]? = some ⟨.dec 3,head+1,halt⟩
  r1 : rows[head+1]? = some ⟨.half 2,head+2,exit⟩
  r2 : rows[head+2]? = some ⟨.inc 3,head+3,head+3⟩
  r3 : rows[head+3]? = some ⟨.inc 3,exit,exit⟩

theorem referenceLiveLayout : LiveLayout originalRows 69 73 35 := by
  constructor <;> decide

theorem candidateLiveLayout : LiveLayout originalRows 146 150 119 := by
  constructor <;> decide

/-- A nonzero decoded next state returns to the next virtual step with exact
selector and tape values and no event. -/
theorem live_generic (rows : Array Row) (head halt exit : Nat) (layout : LiveLayout rows head halt exit)
    (bank : Nat → Nat) (hp : 0 < bank 3) :
    Silent rows ⟨head,bank⟩ ⟨exit,liveBank bank⟩ (liveTime bank) := by
  have hn : bank 3 ≠ 0 := by omega
  let k1 := update (.dec 3) bank
  let k2 := update (.half 2) k1
  have h69 : step rows ⟨head,bank⟩ = (⟨head+1,k1⟩,false) := by
    simp [step,layout.r0,observe,hn,k1]
  have hv : k1 2 = bank 2 := by simp [k1,update]
  by_cases he : bank 2%2=0
  · have h70 : step rows ⟨head+1,k1⟩ = (⟨exit,k2⟩,false) := by
      simp [step,layout.r1,observe,hv,he,k2]
    have heffect : liveBank bank = k2 := by
      funext j
      by_cases h3 : j = 3
      · subst j; simp [liveBank,put,k2,k1,update,he]
      · by_cases h2 : j = 2
        · subst j; simp [liveBank,put,k2,k1,update]
        · simp [liveBank,put,k2,k1,update,h3,h2]
    have h := silent_trans rows _ _ _ 1 1 (silent_one _ _ _ h69) (silent_one _ _ _ h70)
    simpa [liveTime,he,heffect] using h
  · have ho : bank 2%2=1 := by omega
    let k3 := update (.inc 3) k2
    let k4 := update (.inc 3) k3
    have h70 : step rows ⟨head+1,k1⟩ = (⟨head+2,k2⟩,false) := by
      simp [step,layout.r1,observe,hv,he,k2]
    have h71 : step rows ⟨head+2,k2⟩ = (⟨head+3,k3⟩,false) := by
      simp [step,layout.r2,observe,k3]
    have h72 : step rows ⟨head+3,k3⟩ = (⟨exit,k4⟩,false) := by
      simp [step,layout.r3,observe,k4]
    have heffect : liveBank bank = k4 := by
      funext j
      by_cases h3 : j = 3
      · subst j; simp [liveBank,put,k4,k3,k2,k1,update,ho]
      · by_cases h2 : j = 2
        · subst j; simp [liveBank,put,k4,k3,k2,k1,update]
        · simp [liveBank,put,k4,k3,k2,k1,update,h3,h2]
    have h := silent_trans rows _ _ _ 1 1 (silent_one _ _ _ h69) (silent_one _ _ _ h70)
    have h := silent_trans rows _ _ _ 2 1 h (silent_one _ _ _ h71)
    have h := silent_trans rows _ _ _ 3 1 h (silent_one _ _ _ h72)
    simpa [liveTime,he,heffect] using h

theorem live_run (bank : Nat → Nat) (hp : 0 < bank 3) :
    Silent originalRows ⟨69,bank⟩ ⟨35,liveBank bank⟩ (liveTime bank) := by
  simpa using live_generic originalRows 69 73 35 referenceLiveLayout bank hp

def haltBank (bank : Nat → Nat) : Nat → Nat :=
  clear 18 (update (.inc 16) (clear 16 (put 2 (bank 2/2) bank)))

def haltTime (bank : Nat → Nat) : Nat := bank 16 + bank 18 + 5

/-- A zero decoded next state executes the HALT branch, sets the result to
one, clears the branch counter, and returns silently. -/
theorem halt_run (bank : Nat → Nat) (hz : bank 3 = 0) :
    Silent originalRows ⟨69,bank⟩ ⟨15,haltBank bank⟩ (haltTime bank) := by
  let k1 := put 2 (bank 2/2) bank
  let k2 := clear 16 k1
  let k3 := update (.inc 16) k2
  let k4 := clear 18 k3
  have hid := dec_at_zero 3 bank hz
  have h69 : step originalRows ⟨69,bank⟩ = (⟨73,bank⟩,false) := by
    simp [step,originalRows,observe,hz,hid]
  have h73 : step originalRows ⟨73,bank⟩ = (⟨74,k1⟩,false) := by
    have heq : update (.half 2) bank = k1 := by
      funext j
      by_cases hj : j=2 <;> simp [k1,put,update,hj]
    simp [step,originalRows,observe,heq]
  have hfirst := silent_trans originalRows _ _ _ 1 1 (silent_one _ _ _ h69) (silent_one _ _ _ h73)
  have hr74 : originalRows[74]? = some ⟨.dec 16,74,75⟩ := by decide
  have hv16 : k1 16 = bank 16 := by simp [k1,put]
  have hclear16 : Silent originalRows ⟨74,k1⟩ ⟨75,k2⟩ (bank 16+1) :=
    clear_run _ 74 75 16 (bank 16) k1 hr74 hv16
  have h75 : step originalRows ⟨75,k2⟩ = (⟨76,k3⟩,false) := by
    simp [step,originalRows,observe,k3]
  have hr76 : originalRows[76]? = some ⟨.dec 18,76,15⟩ := by decide
  have hv18 : k3 18 = bank 18 := by simp [k3,k2,k1,update,clear,put]
  have hclear18 : Silent originalRows ⟨76,k3⟩ ⟨15,k4⟩ (bank 18+1) :=
    clear_run _ 76 15 18 (bank 18) k3 hr76 hv18
  have h := silent_trans originalRows _ _ _ 2 (bank 16+1) hfirst hclear16
  have h := silent_trans originalRows _ _ _ _ 1 h (silent_one _ _ _ h75)
  have h := silent_trans originalRows _ _ _ _ (bank 18+1) h hclear18
  have ht : haltTime bank = 2+(bank 16+1)+1+(bank 18+1) := by simp [haltTime]; omega
  rw [ht]
  exact h

theorem liveBank_read (bank : Nat → Nat) (j : Nat) :
    liveBank bank j = if j = 3 then bank 3-1+2*(bank 2%2)
      else if j = 2 then bank 2/2 else bank j := by
  rfl

theorem haltBank_read (bank : Nat → Nat) (j : Nat) :
    haltBank bank j = if j = 18 then 0 else if j = 16 then 1
      else if j = 2 then bank 2/2 else bank j := by
  by_cases h18 : j = 18
  · subst j; simp [haltBank,clear]
  · by_cases h16 : j = 16
    · subst j; simp [haltBank,clear,update]
    · by_cases h2 : j = 2
      · subst j; simp [haltBank,clear,update,put]
      · simp [haltBank,clear,update,put,h18,h16,h2]

end Shared.PNP.Record285.SourceVirtualFinish
