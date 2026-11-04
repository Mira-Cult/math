import Shared.PNP.Record285.SourceCandidateClockTotal
import Shared.PNP.Record285.SourceControllerExit

/-! The full comparison and controller exit terminate for arbitrary natural
stores. Correct comparison semantics are supplied separately under the
reachable clean-scratch invariant. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.SourceControllerTotal
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin
open Shared.PNP.Record285.SourceReferenceStart
open Shared.PNP.Record285.SourceComparisonDispatch
open Shared.PNP.Record285.SourceControllerExit
open Shared.PNP.Record285.SourceCandidateClockTotal

/-- Even a non-Boolean positive flag is restored by the two dispatch rows. -/
theorem positive_dispatch (bank : Nat → Nat) (hp : 0 < bank 16) :
    Silent originalRows ⟨154,bank⟩ ⟨172,bank⟩ 2 := by
  let first := update (.dec 16) bank
  have hn : bank 16 ≠ 0 := by omega
  have hs : step originalRows ⟨154,bank⟩ = (⟨155,first⟩,false) := by
    simp [step,originalRows,observe,hn,first]
  have ht : step originalRows ⟨155,first⟩ = (⟨172,update (.inc 16) first⟩,false) := by
    simp [step,originalRows,observe]
  have heffect : update (.inc 16) first = bank := by
    funext j
    by_cases hj : j=16 <;> simp [first,update,hj] <;> omega
  have h := silent_trans originalRows _ _ _ 1 1 (silent_one _ _ _ hs) (silent_one _ _ _ ht)
  simpa [heffect] using h

/-- For every full bank, post-comparison dispatch and its chosen continuation
reach either the next candidate or the next comparison in finite silent time. -/
theorem dispatch_exit_terminates (bank : Nat → Nat) :
    ∃ out duration target, 0 < duration ∧ (target = 1 ∨ target = 6) ∧
      Silent originalRows ⟨154,bank⟩ ⟨target,out⟩ duration := by
  by_cases hz : bank 16 = 0
  · by_cases hr : bank 15 = 0
    · have hdispatch := matching_dispatch bank hz
      simp only [hr,if_true] at hdispatch
      obtain ⟨d,hd,hroll⟩ := rollover_run bank
      exact ⟨rolloverRaw bank,2+d,6,by omega,Or.inr rfl,
        silent_trans originalRows _ _ _ _ _ hdispatch hroll⟩
    · have hdispatch := matching_dispatch bank hz
      simp only [hr,if_false] at hdispatch
      exact ⟨update (.dec 15) bank,2,6,by omega,Or.inr rfl,hdispatch⟩
  · have hp : 0 < bank 16 := by omega
    obtain ⟨d,hd,hadvance⟩ := advance_run bank
    exact ⟨advanceBank bank,2+d,1,by omega,Or.inl rfl,
      silent_trans originalRows _ _ _ _ _ (positive_dispatch bank hp) hadvance⟩

/-- From the start of the reference phase, the entire computation and
controller exit reach the next comparison or candidate on every finite bank.
This termination statement makes no correctness claim for dirty scratch. -/
theorem comparison_and_exit_terminate (bank : Nat → Nat) :
    ∃ out duration target, 0 < duration ∧ (target = 1 ∨ target = 6) ∧
      Silent originalRows ⟨6,bank⟩ ⟨target,out⟩ duration := by
  obtain ⟨mid,d,hd,hcompute⟩ := comparison_compute_terminates bank
  obtain ⟨out,e,target,he,htarget,hexit⟩ := dispatch_exit_terminates mid
  exact ⟨out,d+e,target,by omega,htarget,
    silent_trans originalRows _ _ _ _ _ hcompute hexit⟩

end Shared.PNP.Record285.SourceControllerTotal
