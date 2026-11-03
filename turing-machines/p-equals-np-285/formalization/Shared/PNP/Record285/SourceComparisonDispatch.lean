import Shared.PNP.Record285.SourceCandidateClock

/-! The exact post-comparison dispatch to candidate advance, next input, or
end-of-radix rollover. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SourceComparisonDispatch
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin
open Shared.PNP.Record285.SourceReferenceStart
open Shared.PNP.Record285.SourceReferenceBranch
open Shared.PNP.Record285.SourceReferenceSearch
open Shared.PNP.Record285.SourceUnarySkip
open Shared.PNP.Record285.SourceVirtualStep
open Shared.PNP.Record285.SourceCandidateClock

/-- A nonzero mismatch goes to candidate advance, preserving the full bank. -/
theorem mismatch_dispatch (bank : Nat → Nat) (hbit : bank 16 = 1) :
    Silent originalRows ⟨154,bank⟩ ⟨172,bank⟩ 2 := by
  let first := update (.dec 16) bank
  have hs : step originalRows ⟨154,bank⟩ = (⟨155,first⟩,false) := by
    simp [step,originalRows,observe,hbit,first]
  have ht : step originalRows ⟨155,first⟩ = (⟨172,update (.inc 16) first⟩,false) := by
    simp [step,originalRows,observe]
  have heffect : update (.inc 16) first = bank := by
    funext j
    by_cases hj : j=16 <;> simp [first,update,hbit,hj]
  have h := silent_trans originalRows _ _ _ 1 1 (silent_one _ _ _ hs) (silent_one _ _ _ ht)
  simpa [heffect] using h

/-- A matching candidate continues to the next remaining input, or enters
the radix rollover if none remain. -/
theorem matching_dispatch (bank : Nat → Nat) (hbit : bank 16 = 0) :
    if bank 15 = 0 then Silent originalRows ⟨154,bank⟩ ⟨157,bank⟩ 2
    else Silent originalRows ⟨154,bank⟩ ⟨6,update (.dec 15) bank⟩ 2 := by
  have hid := dec_at_zero 16 bank hbit
  have hs : step originalRows ⟨154,bank⟩ = (⟨156,bank⟩,false) := by
    simp [step,originalRows,observe,hbit,hid]
  by_cases hz : bank 15 = 0
  · have hi := dec_at_zero 15 bank hz
    have ht : step originalRows ⟨156,bank⟩ = (⟨157,bank⟩,false) := by
      simp [step,originalRows,observe,hz,hi]
    simpa [hz] using silent_trans originalRows _ _ _ 1 1 (silent_one _ _ _ hs) (silent_one _ _ _ ht)
  · have ht : step originalRows ⟨156,bank⟩ = (⟨6,update (.dec 15) bank⟩,false) := by
      simp [step,originalRows,observe,hz]
    simpa [hz] using silent_trans originalRows _ _ _ 1 1 (silent_one _ _ _ hs) (silent_one _ _ _ ht)

/-- One complete source comparison followed by its actual graph dispatch.
The remaining rollover and candidate-advance code starts at rows 157 and 172. -/
theorem comparison_and_dispatch (bank : Nat → Nat) (hready : ReferenceReady bank)
    (h6 : bank 6 = 0) (h7 : bank 7 = 0) :
    ∃ out duration, 0 < duration ∧ ReferenceReady out ∧
      (∀ j, Protected j → j ≠ 15 → out j = bank j) ∧
      (if Source.mismatch (bank 11) (bank 12) (bank 13) (bank 14) (bank 15) then
        Silent originalRows ⟨6,bank⟩ ⟨172,out⟩ duration ∧ out 16 = 1 ∧ out 15 = bank 15
       else if bank 15 = 0 then
        Silent originalRows ⟨6,bank⟩ ⟨157,out⟩ duration ∧ out 16 = 0 ∧ out 15 = 0
       else
        Silent originalRows ⟨6,bank⟩ ⟨6,out⟩ duration ∧ out 16 = 0 ∧ out 15+1 = bank 15) := by
  obtain ⟨mid,d,hd,hcompute,hmready,hmframe,hmresult⟩ := comparison_compute_graph bank hready h6 h7
  have hm15 : mid 15 = bank 15 := hmframe 15 (by unfold Protected; omega)
  cases hb : Source.mismatch (bank 11) (bank 12) (bank 13) (bank 14) (bank 15) with
  | true =>
    have hbit : mid 16 = 1 := by simpa [hb] using hmresult
    have hdispatch := mismatch_dispatch mid hbit
    refine ⟨mid,d+2,by omega,hmready,?_,?_⟩
    · intro j hj _; exact hmframe j hj
    · simp only [if_true]
      exact ⟨silent_trans originalRows _ _ _ _ _ hcompute hdispatch,hbit,hm15⟩
  | false =>
    have hbit : mid 16 = 0 := by simpa [hb] using hmresult
    have hdispatch := matching_dispatch mid hbit
    by_cases hz : bank 15 = 0
    · have hmz : mid 15 = 0 := by omega
      simp only [hmz,if_pos] at hdispatch
      refine ⟨mid,d+2,by omega,hmready,?_,?_⟩
      · intro j hj _; exact hmframe j hj
      · simp only [hz,if_true]
        exact ⟨silent_trans originalRows _ _ _ _ _ hcompute hdispatch,hbit,hmz⟩
    · have hmn : mid 15 ≠ 0 := by omega
      simp only [hmn,if_false] at hdispatch
      let out := update (.dec 15) mid
      have hout : ReferenceReady out := by
        simp [ReferenceReady,out,update,hmready.1,hmready.2.1,hmready.2.2]
      have hframe : ∀ j, Protected j → j ≠ 15 → out j = bank j := by
        intro j hj hj15
        simpa [out,update,hj15] using hmframe j hj
      have hout16 : out 16 = 0 := by simp [out,update,hbit]
      have hout15 : out 15+1 = bank 15 := by simp [out,update,hm15]; omega
      refine ⟨out,d+2,by omega,hout,hframe,?_⟩
      simp only [if_false,hz]
      exact ⟨silent_trans originalRows _ _ _ _ _ hcompute hdispatch,hout16,hout15⟩

/-- The complete comparison and branch transfer to reachable pre-control
grammar boundaries with positive bounded progress and no event. -/
theorem comparison_and_dispatch_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨6,bank⟩)
    (hready : ReferenceReady bank) (h6 : bank 6 = 0) (h7 : bank 7 = 0) :
    ∃ out duration, 0 < duration ∧
      PreControlGrammar.acceptedRefinement.boundary t < PreControlGrammar.acceptedRefinement.boundary (t+duration) ∧
      PreControlGrammar.acceptedRefinement.boundary (t+duration) ≤
        PreControlGrammar.acceptedRefinement.boundary t + 32*duration ∧
      ((ProducerGrammar.system PreControlGrammar.grammar).run
        (PreControlGrammar.acceptedRefinement.boundary (t+duration))).bank = out ∧
      ReferenceReady out ∧ (∀ j, Protected j → j ≠ 15 → out j = bank j) ∧
      (if Source.mismatch (bank 11) (bank 12) (bank 13) (bank 14) (bank 15) then
        PreControlGrammar.positions[172]? = some
          ((ProducerGrammar.system PreControlGrammar.grammar).run
            (PreControlGrammar.acceptedRefinement.boundary (t+duration))).pc ∧ out 16 = 1 ∧ out 15 = bank 15
       else if bank 15 = 0 then
        PreControlGrammar.positions[157]? = some
          ((ProducerGrammar.system PreControlGrammar.grammar).run
            (PreControlGrammar.acceptedRefinement.boundary (t+duration))).pc ∧ out 16 = 0 ∧ out 15 = 0
       else PreControlGrammar.positions[6]? = some
          ((ProducerGrammar.system PreControlGrammar.grammar).run
            (PreControlGrammar.acceptedRefinement.boundary (t+duration))).pc ∧ out 16 = 0 ∧ out 15+1 = bank 15) ∧
      (∀ u, PreControlGrammar.acceptedRefinement.boundary t ≤ u →
        u < PreControlGrammar.acceptedRefinement.boundary (t+duration) →
        ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  obtain ⟨out,d,hd,hout,hframe,hcase⟩ := comparison_and_dispatch bank hready h6 h7
  cases hb : Source.mismatch (bank 11) (bank 12) (bank 13) (bank 14) (bank 15) with
  | true =>
    simp only [hb,if_true] at hcase
    obtain ⟨hseg,hbit,hremaining⟩ := hcase
    have h := transfer_silent_graph t d 6 172 bank out hstate hd hseg
    refine ⟨out,d,hd,h.1,h.2.1,h.2.2.2.1,hout,hframe,?_,h.2.2.2.2⟩
    simp only [if_true]
    exact ⟨h.2.2.1,hbit,hremaining⟩
  | false =>
    simp only [hb] at hcase
    by_cases hz : bank 15 = 0
    · simp only [hz,if_true] at hcase
      obtain ⟨hseg,hbit,hremaining⟩ := hcase
      have h := transfer_silent_graph t d 6 157 bank out hstate hd hseg
      refine ⟨out,d,hd,h.1,h.2.1,h.2.2.2.1,hout,hframe,?_,h.2.2.2.2⟩
      simp only [hz,if_true]
      exact ⟨h.2.2.1,hbit,hremaining⟩
    · simp only [hz,if_false] at hcase
      obtain ⟨hseg,hbit,hremaining⟩ := hcase
      have h := transfer_silent_graph t d 6 6 bank out hstate hd hseg
      refine ⟨out,d,hd,h.1,h.2.1,h.2.2.2.1,hout,hframe,?_,h.2.2.2.2⟩
      simp only [if_false,hz]
      exact ⟨h.2.2.1,hbit,hremaining⟩

end Shared.PNP.Record285.SourceComparisonDispatch
