import Shared.PNP.Record285.SourceVirtualFinish
import Shared.PNP.Record285.SourceVirtualLoop

/-! The complete checked reference virtual step and its readiness invariant. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SourceVirtualStep
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin
open Shared.PNP.Record285.SourceReferenceStart
open Shared.PNP.Record285.SourceReferenceBranch
open Shared.PNP.Record285.SourceReferenceSearch
open Shared.PNP.Record285.SourceVirtualLoop
open Shared.PNP.Record285.SourceUnarySkip
open Shared.PNP.Record285.SourceChoiceStep
open Shared.PNP.Record285.SourceReferenceProgram
open Shared.PNP.Record285.SourceVirtualAction
open Shared.PNP.Record285.SourceVirtualFinish

def ReferenceReady (bank : Nat → Nat) : Prop := bank 4 = 0 ∧ bank 5 = 0 ∧ bank 17 = 0

def packed (bank : Nat → Nat) : Nat :=
  (Source.popUnary (Source.skipUnary
    ((referenceSimState bank).selector + (referenceSimState bank).choices%2) (bank 14+bank 15))).1

def virtualLeft (bank : Nat → Nat) : Nat := if (packed bank/2)%2=0 then bank 19 else bank 2
def virtualRight (bank : Nat → Nat) : Nat := if (packed bank/2)%2=0 then bank 2 else bank 19

def virtualNext (bank : Nat → Nat) : Source.SimState :=
  ⟨2*virtualLeft bank + packed bank%2,virtualRight bank/2,
   packed bank/4-1+2*(virtualRight bank%2),bank 0/2⟩

theorem source_step_view (bank : Nat → Nat) :
    Source.simStep (bank 14+bank 15) (referenceSimState bank) =
      if packed bank/4=0 then none else some (virtualNext bank) := by
  rfl

/-- Full information needed at the live/HALT decision boundary. -/
structure CoreFacts (bank core : Nat → Nat) : Prop where
  selector : core 3 = packed bank/4
  right : core 2 = virtualRight bank
  left : core 19 = 2*virtualLeft bank + packed bank%2
  choice : core 0 = bank 0/2
  clock : core 20 = bank 20-1
  scratch4 : core 4 = 0
  scratch5 : core 5 = 0
  scratch17 : core 17 = 0
  expected : core 16 = bank 16
  branches : core 18 = bank 18
  frame : ∀ j, Protected j → core j = bank j

/-- The checked decoder and both direction paths establish the complete
source-state relation at the row-69 decision boundary. -/
theorem prepared_core_facts (bank : Nat → Nat) (hready : ReferenceReady bank) :
    CoreFacts bank (actionCore (recordDecodedBank bank)) := by
  obtain ⟨h4,h5,h17⟩ := hready
  let record := recordDecodedBank bank
  have hm := record_matches_source bank h4 h5
  change record 3 = _ ∧ record 1 = _ ∧ record 0 = _ ∧ record 20 = _ ∧ _ at hm
  obtain ⟨hr3,hr1,hr0,hr20,hrframe⟩ := hm
  have hrframe' : ∀ j, j ≠ 1 → j ≠ 3 → j ≠ 0 → j ≠ 20 → record j = bank j := hrframe
  have hpacked : record 3 = packed bank := by simpa [packed] using hr3
  have hr2 : record 2 = bank 2 := hrframe' 2 (by decide) (by decide) (by decide) (by decide)
  have hr19 : record 19 = bank 19 := hrframe' 19 (by decide) (by decide) (by decide) (by decide)
  have hr5 : record 5 = 0 := by rw [hrframe' 5 (by decide) (by decide) (by decide) (by decide),h5]
  have hleft : actionLeft record = virtualLeft bank := by simp [actionLeft,virtualLeft,hpacked,hr2,hr19]
  have hright : actionRight record = virtualRight bank := by simp [actionRight,virtualRight,hpacked,hr2,hr19]
  obtain ⟨hc3,hc2,hc19,hc5,hcframe⟩ := action_core_values record
  refine ⟨?_,?_,?_,?_,?_,?_,hc5,?_,?_,?_,?_⟩
  · rw [hc3,hpacked]
  · rw [hc2,hright]
  · rw [hc19,hr5,hpacked,hleft]
    omega
  · rw [hcframe 0 (by decide) (by decide) (by decide) (by decide)]
    simpa [referenceSimState] using hr0
  · rw [hcframe 20 (by decide) (by decide) (by decide) (by decide)]
    exact hr20
  · rw [hcframe 4 (by decide) (by decide) (by decide) (by decide),
      hrframe' 4 (by decide) (by decide) (by decide) (by decide),h4]
  · rw [hcframe 17 (by decide) (by decide) (by decide) (by decide),
      hrframe' 17 (by decide) (by decide) (by decide) (by decide),h17]
  · rw [hcframe 16 (by decide) (by decide) (by decide) (by decide),
      hrframe' 16 (by decide) (by decide) (by decide) (by decide)]
  · rw [hcframe 18 (by decide) (by decide) (by decide) (by decide),
      hrframe' 18 (by decide) (by decide) (by decide) (by decide)]
  · intro j hj
    have h1 : j ≠ 1 := by simp only [Protected] at hj; omega
    have h3 : j ≠ 3 := by simp only [Protected] at hj; omega
    have h0 : j ≠ 0 := by simp only [Protected] at hj; omega
    have h20 : j ≠ 20 := by simp only [Protected] at hj; omega
    have h2 : j ≠ 2 := by simp only [Protected] at hj; omega
    have h19 : j ≠ 19 := by simp only [Protected] at hj; omega
    have h5j : j ≠ 5 := by simp only [Protected] at hj; omega
    exact (hcframe j h3 h2 h19 h5j).trans (hrframe' j h1 h3 h0 h20)

/-- The complete decoded prefix always decrements the clock, even for dirty
scratch; source-value correctness is a separate, stronger assertion. -/
theorem decoded_clock (bank : Nat → Nat) : recordDecodedBank bank 20 = bank 20-1 := by
  have h := choiceBank_read bank 20
  simpa [recordDecodedBank,recordBank,decodedBank,afterSkip,preparedBank,afterProgramRaw,put] using h

/-- Every graph-level evaluator iteration terminates silently on arbitrary
banks. If it continues, its natural clock decreases by exactly one. -/
theorem raw_iteration_progress (bank : Nat → Nat) (hp : 0 < bank 20) :
    ∃ out duration, 0 < duration ∧
      ((Silent originalRows ⟨35,bank⟩ ⟨15,out⟩ duration ∧ out 18 = 0) ∨
        (Silent originalRows ⟨35,bank⟩ ⟨35,out⟩ duration ∧ out 20+1 = bank 20 ∧ out 18 = bank 18)) := by
  let record := recordDecodedBank bank
  let core := actionCore record
  have hprefix := record_prefix_raw bank hp
  change Silent originalRows ⟨35,bank⟩ ⟨56,record⟩ (recordPrefixTime bank) at hprefix
  obtain ⟨d,hd,hcore⟩ := action_core_run record
  change Silent originalRows ⟨56,record⟩ ⟨69,core⟩ d at hcore
  have hfirst := silent_trans originalRows _ _ _ (recordPrefixTime bank) d hprefix hcore
  have hcv := action_core_values record
  have hclock : core 20 = bank 20-1 := by
    have hf := hcv.2.2.2.2 20 (by decide) (by decide) (by decide) (by decide)
    exact hf.trans (decoded_clock bank)
  have hbranches : core 18 = bank 18 := by
    have hf := hcv.2.2.2.2 18 (by decide) (by decide) (by decide) (by decide)
    have hr := choiceBank_read bank 18
    have hr' : record 18 = bank 18 := by
      simpa [record,recordDecodedBank,recordBank,decodedBank,afterSkip,preparedBank,afterProgramRaw,put] using hr
    exact hf.trans hr'
  by_cases hz : core 3 = 0
  · have hlast := halt_run core hz
    have hsegment := silent_trans originalRows _ _ _ _ _ hfirst hlast
    have hzero : haltBank core 18 = 0 := by simp [haltBank_read]
    exact ⟨haltBank core,recordPrefixTime bank+d+haltTime core,by omega,Or.inl ⟨hsegment,hzero⟩⟩
  · have hpositive : 0 < core 3 := by omega
    have hlast := live_run core hpositive
    have hsegment := silent_trans originalRows _ _ _ _ _ hfirst hlast
    have hnext : liveBank core 20+1 = bank 20 := by
      simp [liveBank_read,hclock]
      omega
    have hcount : liveBank core 18 = bank 18 := by simp [liveBank_read,hbranches]
    exact ⟨liveBank core,recordPrefixTime bank+d+liveTime core,by omega,Or.inr ⟨hsegment,hnext,hcount⟩⟩

/-- Every finite evaluator clock terminates in a silent return for arbitrary
initial stores, without assuming the scratch invariant. -/
theorem raw_evaluator_terminates (clock : Nat) (bank : Nat → Nat) (hclock : bank 20 = clock) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨35,bank⟩ ⟨15,out⟩ duration ∧ out 18 ≤ bank 18 := by
  induction clock generalizing bank with
  | zero =>
    have hz : bank 20 = 0 := hclock
    have hid := dec_at_zero 20 bank hz
    have hs : step originalRows ⟨35,bank⟩ = (⟨15,bank⟩,false) := by
      simp [step,originalRows,observe,hz,hid]
    exact ⟨bank,1,by decide,silent_one originalRows _ _ hs,by omega⟩
  | succ clock ih =>
    have hp : 0 < bank 20 := by omega
    obtain ⟨mid,d,hd,hcase⟩ := raw_iteration_progress bank hp
    rcases hcase with ⟨hhalt,hzero⟩ | ⟨hcontinue,hnext,hcount⟩
    · exact ⟨mid,d,hd,hhalt,by omega⟩
    · have hm : mid 20 = clock := by omega
      obtain ⟨out,e,he,hrest,hbound⟩ := ih mid hm
      exact ⟨out,d+e,by omega,silent_trans originalRows _ _ _ _ _ hcontinue hrest,by omega⟩

/-- Arbitrary-store finite progress transfers to the exact pre-control
grammar, independently of whether the scratch contents encode a source run. -/
theorem raw_evaluator_terminates_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨35,bank⟩) :
    ∃ out duration, 0 < duration ∧
      PreControlGrammar.acceptedRefinement.boundary t <
        PreControlGrammar.acceptedRefinement.boundary (t+duration) ∧
      PreControlGrammar.positions[15]? = some
        ((ProducerGrammar.system PreControlGrammar.grammar).run
          (PreControlGrammar.acceptedRefinement.boundary (t+duration))).pc ∧
      ((ProducerGrammar.system PreControlGrammar.grammar).run
        (PreControlGrammar.acceptedRefinement.boundary (t+duration))).bank = out ∧
      (∀ u, PreControlGrammar.acceptedRefinement.boundary t ≤ u →
        u < PreControlGrammar.acceptedRefinement.boundary (t+duration) →
        ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  obtain ⟨out,d,hd,hseg,hcount⟩ := raw_evaluator_terminates (bank 20) bank rfl
  have h := transfer_silent_graph t d 35 15 bank out hstate hd hseg
  exact ⟨out,d,hd,h.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩

/-- The outer reference branch loop also terminates for arbitrary stores:
each positive branch reduces its counter, and the evaluator cannot increase it. -/
theorem raw_reference_loop_terminates (branches : Nat) (bank : Nat → Nat)
    (hbranches : bank 18 = branches) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨15,bank⟩ ⟨77,out⟩ duration ∧ out 18 = 0 := by
  induction branches using Nat.strongRecOn generalizing bank with
  | ind branches ih =>
    by_cases hz : branches = 0
    · have hb : bank 18 = 0 := by omega
      exact ⟨bank,1,by decide,zero_branch bank hb,hb⟩
    · have hp : 0 < bank 18 := by omega
      let prepared := afterBranchRaw bank
      have hbranch := positive_branch_raw bank hp
      have hdecrease : prepared 18 < branches := by
        simp [prepared,afterBranchRaw_view,branchView]
        omega
      obtain ⟨next,d,hd,heval,hbound⟩ := raw_evaluator_terminates (prepared 20) prepared rfl
      have hsmall : next 18 < branches := by omega
      obtain ⟨out,e,he,hrest,hzero⟩ := ih (next 18) hsmall next rfl
      have hq := silent_trans originalRows _ _ _ _ _ hbranch heval
      have hq := silent_trans originalRows _ _ _ _ _ hq hrest
      exact ⟨out,branchTime bank+d+e,by omega,hq,hzero⟩

/-- The entire reference phase terminates silently for every finite bank,
without assuming that scratch values encode a valid source computation. -/
theorem raw_reference_phase_terminates (bank : Nat → Nat) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨6,bank⟩ ⟨77,out⟩ duration ∧ out 18 = 0 := by
  have hsetup := reference_setup_raw bank
  let prepared := afterReferenceRaw bank
  obtain ⟨out,d,hd,hloop,hzero⟩ := raw_reference_loop_terminates (prepared 18) prepared rfl
  have hq := silent_trans originalRows _ _ _ _ _ hsetup hloop
  exact ⟨out,setupTime bank+d,by omega,hq,hzero⟩

/-- Arbitrary-store reference-phase progress transfers to the exact grammar;
source-result correctness still requires the explicit clean-scratch invariant. -/
theorem raw_reference_phase_terminates_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨6,bank⟩) :
    ∃ out duration, 0 < duration ∧
      PreControlGrammar.acceptedRefinement.boundary t <
        PreControlGrammar.acceptedRefinement.boundary (t+duration) ∧
      PreControlGrammar.positions[77]? = some
        ((ProducerGrammar.system PreControlGrammar.grammar).run
          (PreControlGrammar.acceptedRefinement.boundary (t+duration))).pc ∧
      ((ProducerGrammar.system PreControlGrammar.grammar).run
        (PreControlGrammar.acceptedRefinement.boundary (t+duration))).bank = out ∧ out 18 = 0 ∧
      (∀ u, PreControlGrammar.acceptedRefinement.boundary t ≤ u →
        u < PreControlGrammar.acceptedRefinement.boundary (t+duration) →
        ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  obtain ⟨out,d,hd,hseg,hzero⟩ := raw_reference_phase_terminates bank
  have h := transfer_silent_graph t d 6 77 bank out hstate hd hseg
  exact ⟨out,d,hd,h.1,h.2.2.1,h.2.2.2.1,hzero,h.2.2.2.2⟩

/-- The checked source virtual-step contract holds with three explicit
zero-scratch slots. This covers arbitrary virtual states and positive clocks. -/
theorem reference_single_step : SingleStepInterface ReferenceReady where
  scratch := by
    intro bank h
    exact ⟨h.1,h.2.2⟩
  after_setup := by
    intro bank h hp
    simp [ReferenceReady,afterBranchRaw_view,branchView,h.2.1]
  execute_step := by
    intro bank hready hexpected hp
    let record := recordDecodedBank bank
    let core := actionCore record
    have hprefix := record_prefix_raw bank hp
    change Silent originalRows ⟨35,bank⟩ ⟨56,record⟩ (recordPrefixTime bank) at hprefix
    obtain ⟨d,hd,hcore⟩ := action_core_run record
    change Silent originalRows ⟨56,record⟩ ⟨69,core⟩ d at hcore
    have hfirst := silent_trans originalRows _ _ _ (recordPrefixTime bank) d hprefix hcore
    have hf : CoreFacts bank core := prepared_core_facts bank hready
    by_cases hz : packed bank/4 = 0
    · have hzero : core 3 = 0 := by rw [hf.selector,hz]
      let out := haltBank core
      have hlast := halt_run core hzero
      have hsegment := silent_trans originalRows _ _ _ _ _ hfirst hlast
      have hout : ReferenceReady out := by
        simp [ReferenceReady,out,haltBank_read,hf.scratch4,hf.scratch5,hf.scratch17]
      have hframe : ∀ j, Protected j → out j = bank j := by
        intro j hj
        have h18 : j ≠ 18 := by simp only [Protected] at hj; omega
        have h16 : j ≠ 16 := by simp only [Protected] at hj; omega
        have h2 : j ≠ 2 := by simp only [Protected] at hj; omega
        simp [out,haltBank_read,h18,h16,h2,hf.frame j hj]
      have hcount : out 18 = 0 := by simp [out,haltBank_read]
      have hresult : out 16 = 1 := by simp [out,haltBank_read]
      refine ⟨out,recordPrefixTime bank+d+haltTime core,by omega,hout,hframe,?_⟩
      rw [source_step_view]
      simp only [hz,if_pos]
      exact ⟨hsegment,hcount,hresult⟩
    · have hpositive : 0 < core 3 := by rw [hf.selector]; omega
      let out := liveBank core
      have hlast := live_run core hpositive
      have hsegment := silent_trans originalRows _ _ _ _ _ hfirst hlast
      have hout : ReferenceReady out := by
        simp [ReferenceReady,out,liveBank_read,hf.scratch4,hf.scratch5,hf.scratch17]
      have hframe : ∀ j, Protected j → out j = bank j := by
        intro j hj
        have h3 : j ≠ 3 := by simp only [Protected] at hj; omega
        have h2 : j ≠ 2 := by simp only [Protected] at hj; omega
        simp [out,liveBank_read,h3,h2,hf.frame j hj]
      have hclock : out 20+1 = bank 20 := by
        simp [out,liveBank_read,hf.clock]
        omega
      have hsim : referenceSimState out = virtualNext bank := by
        simp [referenceSimState,virtualNext,out,liveBank_read,hf.left,hf.right,hf.selector,hf.choice]
      have hcount : out 18 = bank 18 := by simp [out,liveBank_read,hf.branches]
      have hresult : out 16 = 0 := by simp [out,liveBank_read,hf.expected,hexpected]
      refine ⟨out,recordPrefixTime bank+d+liveTime core,by omega,hout,hframe,?_⟩
      rw [source_step_view]
      simp only [hz]
      exact ⟨hsegment,hclock,hsim,hcount,hresult⟩

/-- Every reachable positive-clock reference step transfers to the exact
pre-control grammar, with full output bank, matching HALT/live outcome,
positive bounded progress, protected-frame preservation and no events. -/
theorem reference_single_step_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨35,bank⟩)
    (hready : ReferenceReady bank) (hexpected : bank 16 = 0) (hp : 0 < bank 20) :
    ∃ out duration, 0 < duration ∧
      PreControlGrammar.acceptedRefinement.boundary t <
        PreControlGrammar.acceptedRefinement.boundary (t+duration) ∧
      PreControlGrammar.acceptedRefinement.boundary (t+duration) ≤
        PreControlGrammar.acceptedRefinement.boundary t + 32*duration ∧
      ((ProducerGrammar.system PreControlGrammar.grammar).run
        (PreControlGrammar.acceptedRefinement.boundary (t+duration))).bank = out ∧
      ReferenceReady out ∧ (∀ j, Protected j → out j = bank j) ∧
      (match Source.simStep (bank 14+bank 15) (referenceSimState bank) with
       | none => PreControlGrammar.positions[15]? = some
           ((ProducerGrammar.system PreControlGrammar.grammar).run
             (PreControlGrammar.acceptedRefinement.boundary (t+duration))).pc ∧ out 18 = 0 ∧ out 16 = 1
       | some next => PreControlGrammar.positions[35]? = some
           ((ProducerGrammar.system PreControlGrammar.grammar).run
             (PreControlGrammar.acceptedRefinement.boundary (t+duration))).pc ∧
           out 20+1 = bank 20 ∧ referenceSimState out = next ∧ out 18 = bank 18 ∧ out 16 = 0) ∧
      (∀ u, PreControlGrammar.acceptedRefinement.boundary t ≤ u →
        u < PreControlGrammar.acceptedRefinement.boundary (t+duration) →
        ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  obtain ⟨out,d,hd,hout,hframe,hcase⟩ := reference_single_step.execute_step bank hready hexpected hp
  cases hs : Source.simStep (bank 14+bank 15) (referenceSimState bank) with
  | none =>
    simp only [hs] at hcase
    obtain ⟨hseg,hcount,hresult⟩ := hcase
    have h := transfer_silent_graph t d 35 15 bank out hstate hd hseg
    refine ⟨out,d,hd,h.1,h.2.1,h.2.2.2.1,hout,hframe,?_,h.2.2.2.2⟩
    exact ⟨h.2.2.1,hcount,hresult⟩
  | some next =>
    simp only [hs] at hcase
    obtain ⟨hseg,hclock,hsim,hcount,hresult⟩ := hcase
    have h := transfer_silent_graph t d 35 35 bank out hstate hd hseg
    refine ⟨out,d,hd,h.1,h.2.1,h.2.2.2.1,hout,hframe,?_,h.2.2.2.2⟩
    exact ⟨h.2.2.1,hclock,hsim,hcount,hresult⟩

/-- The arbitrary-clock bounded evaluator is now discharged for the explicit
scratch invariant. -/
theorem reference_evaluator : EvaluationInterface ReferenceReady :=
  evaluator_of_single_step ReferenceReady reference_single_step

/-- The complete reference search terminates silently for every finite clock
and branch count under the stated readiness and expected-value conditions. -/
theorem reference_search_all_clocks (branches : Nat) (bank : Nat → Nat)
    (hready : ReferenceReady bank) (hexpected : bank 16 = 0) (hbranches : bank 18 = branches) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨15,bank⟩ ⟨77,out⟩ duration ∧
      ReferenceReady out ∧ out 18 = 0 ∧
      out 16 = (if Source.referenceSearch (bank 14+bank 15) (bank 13) branches then 1 else 0) ∧
      (∀ j, Protected j → out j = bank j) :=
  reference_search_graph ReferenceReady reference_evaluator branches bank hready hexpected hbranches

/-- From row 6, the complete reference phase agrees with the source reference,
with finite silent execution and the entire protected frame preserved. -/
theorem reference_phase_all_clocks (bank : Nat → Nat) (hready : ReferenceReady bank) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨6,bank⟩ ⟨77,out⟩ duration ∧
      ReferenceReady out ∧ out 18 = 0 ∧
      out 16 = (if Source.reference (bank 13) (bank 14) (bank 15) then 1 else 0) ∧
      (∀ j, Protected j → out j = bank j) := by
  have hafter : ReferenceReady (afterReferenceRaw bank) := by
    simp [ReferenceReady,afterReferenceRaw,hready.2.1]
  exact reference_phase_graph ReferenceReady reference_evaluator bank hready.1 hready.2.2 hafter

/-- The complete arbitrary-clock reference phase on the exact pre-control
grammar, with positive bounded progress and no event. -/
theorem reference_phase_all_clocks_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨6,bank⟩) (hready : ReferenceReady bank) :
    ∃ out duration, 0 < duration ∧
      PreControlGrammar.acceptedRefinement.boundary t <
        PreControlGrammar.acceptedRefinement.boundary (t+duration) ∧
      PreControlGrammar.acceptedRefinement.boundary (t+duration) ≤
        PreControlGrammar.acceptedRefinement.boundary t + 32*duration ∧
      PreControlGrammar.positions[77]? = some
        ((ProducerGrammar.system PreControlGrammar.grammar).run
          (PreControlGrammar.acceptedRefinement.boundary (t+duration))).pc ∧
      ((ProducerGrammar.system PreControlGrammar.grammar).run
        (PreControlGrammar.acceptedRefinement.boundary (t+duration))).bank = out ∧
      ReferenceReady out ∧ out 18 = 0 ∧
      out 16 = (if Source.reference (bank 13) (bank 14) (bank 15) then 1 else 0) ∧
      (∀ j, Protected j → out j = bank j) ∧
      (∀ u, PreControlGrammar.acceptedRefinement.boundary t ≤ u →
        u < PreControlGrammar.acceptedRefinement.boundary (t+duration) →
        ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  have hafter : ReferenceReady (afterReferenceRaw bank) := by
    simp [ReferenceReady,afterReferenceRaw,hready.2.1]
  exact reference_phase_to_grammar ReferenceReady reference_evaluator t bank hstate hready.1 hready.2.2 hafter

end Shared.PNP.Record285.SourceVirtualStep
