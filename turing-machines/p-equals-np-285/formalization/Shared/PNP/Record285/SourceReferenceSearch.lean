import Shared.PNP.Record285.SourceReferenceBranch

/-! Composition of the reference branch loop. `EvaluationInterface` exposes
all remaining assumptions about the bounded virtual evaluator: finite positive
silent execution, its exact HALT observation, preservation of the protected
bank and restoration of the declared readiness invariant. No instance for
arbitrary clocks is asserted here. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SourceReferenceSearch
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin
open Shared.PNP.Record285.SourceReferenceStart
open Shared.PNP.Record285.SourceReferenceBranch

/-- The two other micro-registers, omitted slots, program, exponent, input
parameters, and the entire unbounded tail are protected by a reference branch. -/
def Protected (j : Nat) : Prop := (6 ≤ j ∧ j ≤ 15) ∨ 21 ≤ j

/-- Explicit contract for a bounded evaluator. `Ready` must describe all
additional retained scratch/representation state; an instance is proved in
`SourceVirtualStep`. -/
structure EvaluationInterface (Ready : (Nat → Nat) → Prop) : Prop where
  scratch : ∀ bank, Ready bank → bank 4 = 0 ∧ bank 17 = 0
  after_setup : ∀ bank, Ready bank → 0 < bank 18 → Ready (afterBranchRaw bank)
  execute : ∀ bank, Ready bank → bank 16 = 0 → bank 20 = bank 13 →
    referenceSimState bank = ⟨0,0,0,bank 18⟩ →
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨35,bank⟩ ⟨15,out⟩ duration ∧
      Ready out ∧ (∀ j, Protected j → out j = bank j) ∧
      out 18 = (if Source.haltedWithin (bank 14+bank 15) (bank 13) (referenceSimState bank) then 0 else bank 18) ∧
      out 16 = (if Source.haltedWithin (bank 14+bank 15) (bank 13) (referenceSimState bank) then 1 else 0)

/-- Branch preparation preserves every protected slot, including all slots
above the finite producer bank. -/
theorem branch_protected (bank : Nat → Nat) (h4 : bank 4 = 0) (j : Nat) (hj : Protected j) :
    afterBranchRaw bank j = bank j := by
  rw [afterBranchRaw_view]
  have h2 : j ≠ 2 := by simp only [Protected] at hj; omega
  have h3 : j ≠ 3 := by simp only [Protected] at hj; omega
  have h4j : j ≠ 4 := by simp only [Protected] at hj; omega
  have h17 : j ≠ 17 := by simp only [Protected] at hj; omega
  have h19 : j ≠ 19 := by simp only [Protected] at hj; omega
  have h20 : j ≠ 20 := by simp only [Protected] at hj; omega
  have h18 : j ≠ 18 := by simp only [Protected] at hj; omega
  have h0 : j ≠ 0 := by simp only [Protected] at hj; omega
  by_cases h13 : j = 13
  · subst j; simp [branchView,h4]
  · simp [branchView,h2,h3,h4j,h17,h19,h13,h20,h18,h0]

/-- Conditional only on the displayed evaluator interface: the complete
finite reference-search loop terminates, emits no event, returns the exact
`Source.referenceSearch` result, and preserves the complete protected frame. -/
theorem reference_search_graph (Ready : (Nat → Nat) → Prop) (E : EvaluationInterface Ready)
    (branches : Nat) (bank : Nat → Nat) (hready : Ready bank)
    (hexpected : bank 16 = 0) (hbranches : bank 18 = branches) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨15,bank⟩ ⟨77,out⟩ duration ∧
      Ready out ∧ out 18 = 0 ∧
      out 16 = (if Source.referenceSearch (bank 14+bank 15) (bank 13) branches then 1 else 0) ∧
      (∀ j, Protected j → out j = bank j) := by
  induction branches generalizing bank with
  | zero =>
    have hz : bank 18 = 0 := by omega
    refine ⟨bank,1,by decide,zero_branch bank hz,hready,hz,?_,?_⟩
    · simp [Source.referenceSearch,hexpected]
    · intro j hj; rfl
  | succ branches ih =>
    have hp : 0 < bank 18 := by omega
    obtain ⟨h4,h17⟩ := E.scratch bank hready
    let mid := afterBranchRaw bank
    have hmidReady : Ready mid := E.after_setup bank hready hp
    have hsetup := positive_branch_raw bank hp
    have hmid18 : mid 18 = branches := by
      simp [mid,afterBranchRaw_view,branchView]
      omega
    have hmid16 : mid 16 = 0 := by simp [mid,afterBranchRaw_view,branchView,hexpected]
    have hmid13 : mid 13 = bank 13 := branch_protected bank h4 13 (by unfold Protected; omega)
    have hmid14 : mid 14 = bank 14 := branch_protected bank h4 14 (by unfold Protected; omega)
    have hmid15 : mid 15 = bank 15 := branch_protected bank h4 15 (by unfold Protected; omega)
    have hmodel := branch_matches_reference bank h4 h17
    have hclock : mid 20 = mid 13 := by
      change afterBranchRaw bank 20 = afterBranchRaw bank 13
      rw [hmodel.2.1]
      exact hmid13.symm
    have hinit : referenceSimState mid = ⟨0,0,0,mid 18⟩ := by
      change referenceSimState (afterBranchRaw bank) = _
      rw [hmodel.1,hmid18]
      congr 1
      omega
    obtain ⟨next,d,hd,heval,hnextReady,hframe,hcount,hresult⟩ :=
      E.execute mid hmidReady hmid16 hclock hinit
    let bit := Source.haltedWithin (bank 14+bank 15) (bank 13) ⟨0,0,0,branches⟩
    have hbit : Source.haltedWithin (mid 14+mid 15) (mid 13) (referenceSimState mid) = bit := by
      simp [bit,hmid14,hmid15,hmid13,hinit,hmid18]
    rw [hbit] at hcount hresult
    cases hb : bit with
    | true =>
      have hzero : next 18 = 0 := by simpa [hb] using hcount
      have hres : next 16 = 1 := by simpa [hb] using hresult
      have hfinish := zero_branch next hzero
      have hq := silent_trans originalRows _ _ _ _ _ hsetup heval
      have hq := silent_trans originalRows _ _ _ _ _ hq hfinish
      refine ⟨next,branchTime bank+d+1,by omega,hq,hnextReady,hzero,?_,?_⟩
      · have hb' : Source.haltedWithin (bank 14+bank 15) (bank 13) ⟨0,0,0,branches⟩ = true := by
          simpa [bit] using hb
        simp [Source.referenceSearch,hb',hres]
      · intro j hj
        exact (hframe j hj).trans (branch_protected bank h4 j hj)
    | false =>
      have hnextCount : next 18 = branches := by simpa [hb,hmid18] using hcount
      have hnextResult : next 16 = 0 := by simpa [hb] using hresult
      obtain ⟨out,e,he,hrest,houtReady,houtCount,houtResult,houtFrame⟩ :=
        ih next hnextReady hnextResult hnextCount
      have hnext13 : next 13 = bank 13 := (hframe 13 (by unfold Protected; omega)).trans hmid13
      have hnext14 : next 14 = bank 14 := (hframe 14 (by unfold Protected; omega)).trans hmid14
      have hnext15 : next 15 = bank 15 := (hframe 15 (by unfold Protected; omega)).trans hmid15
      have hq := silent_trans originalRows _ _ _ _ _ hsetup heval
      have hq := silent_trans originalRows _ _ _ _ _ hq hrest
      refine ⟨out,branchTime bank+d+e,by omega,hq,houtReady,houtCount,?_,?_⟩
      · rw [houtResult,hnext14,hnext15,hnext13]
        have hb' : Source.haltedWithin (bank 14+bank 15) (bank 13) ⟨0,0,0,branches⟩ = false := by
          simpa [bit] using hb
        simp [Source.referenceSearch,hb']
      · intro j hj
        exact (houtFrame j hj).trans ((hframe j hj).trans (branch_protected bank h4 j hj))

/-- Readiness for zero-clock evaluation. Other scratch and data cells remain
arbitrary; only the two slots used by branch copying must be zero. -/
def ZeroReady (bank : Nat → Nat) : Prop := bank 13 = 0 ∧ bank 4 = 0 ∧ bank 17 = 0

/-- The open evaluator interface is fully discharged at clock zero: the
actual row-35 zero test returns silently to the branch controller. -/
theorem zero_evaluation_interface : EvaluationInterface ZeroReady where
  scratch := by
    intro bank h
    exact ⟨h.2.1,h.2.2⟩
  after_setup := by
    intro bank h hp
    simp [ZeroReady,afterBranchRaw_view,branchView,h.1,h.2.1]
  execute := by
    intro bank hready hexpected hclock hinit
    have hzero : bank 20 = 0 := by rw [hclock,hready.1]
    have hdec := dec_at_zero 20 bank hzero
    have hstep : step originalRows ⟨35,bank⟩ = (⟨15,bank⟩,false) := by
      simp [step,originalRows,observe,hzero,hdec]
    have hquiet : Silent originalRows ⟨35,bank⟩ ⟨15,bank⟩ 1 :=
      silent_one originalRows _ _ hstep
    refine ⟨bank,1,by decide,hquiet,hready,?_,?_,?_⟩
    · intro j hj; rfl
    · simp [hready.1]
    · simp [hready.1,hexpected]

/-- Every finite zero-clock branch search terminates silently and returns
false, preserving the protected bank; all nondeclared registers may be
arbitrary at entry. -/
theorem zero_clock_reference_graph (branches : Nat) (bank : Nat → Nat)
    (hclock : bank 13 = 0) (h4 : bank 4 = 0) (h17 : bank 17 = 0)
    (hexpected : bank 16 = 0) (hbranches : bank 18 = branches) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨15,bank⟩ ⟨77,out⟩ duration ∧
      ZeroReady out ∧ out 18 = 0 ∧ out 16 = 0 ∧
      (∀ j, Protected j → out j = bank j) := by
  obtain ⟨out,d,hd,hquiet,hready,hcount,hresult,hframe⟩ :=
    reference_search_graph ZeroReady zero_evaluation_interface branches bank
      ⟨hclock,h4,h17⟩ hexpected hbranches
  refine ⟨out,d,hd,hquiet,hready,hcount,?_,hframe⟩
  simpa [hclock] using hresult

/-- The conditional all-clock reference loop transfers to the exact checked
grammar with a positive bounded time map, exact resulting bank, and no event. -/
theorem reference_search_to_grammar (Ready : (Nat → Nat) → Prop) (E : EvaluationInterface Ready)
    (t branches : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨15,bank⟩)
    (hready : Ready bank) (hexpected : bank 16 = 0) (hbranches : bank 18 = branches) :
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
      Ready out ∧ out 18 = 0 ∧
      out 16 = (if Source.referenceSearch (bank 14+bank 15) (bank 13) branches then 1 else 0) ∧
      (∀ j, Protected j → out j = bank j) ∧
      (∀ u, PreControlGrammar.acceptedRefinement.boundary t ≤ u →
        u < PreControlGrammar.acceptedRefinement.boundary (t+duration) →
        ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  obtain ⟨out,d,hd,hseg,hout,hcount,hresult,hframe⟩ :=
    reference_search_graph Ready E branches bank hready hexpected hbranches
  have hphysical := transfer_silent_graph t d 15 77 bank out hstate hd hseg
  exact ⟨out,d,hd,hphysical.1,hphysical.2.1,hphysical.2.2.1,hphysical.2.2.2.1,
    hout,hcount,hresult,hframe,hphysical.2.2.2.2⟩

/-- The zero-clock specialization is unconditional apart from the explicit
reachable boundary and clean-scratch hypotheses; it covers every finite branch
count and preserves the complete protected frame. -/
theorem zero_clock_reference_to_grammar (t branches : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨15,bank⟩)
    (hclock : bank 13 = 0) (h4 : bank 4 = 0) (h17 : bank 17 = 0)
    (hexpected : bank 16 = 0) (hbranches : bank 18 = branches) :
    ∃ out duration, 0 < duration ∧
      PreControlGrammar.acceptedRefinement.boundary t <
        PreControlGrammar.acceptedRefinement.boundary (t+duration) ∧
      PreControlGrammar.positions[77]? = some
        ((ProducerGrammar.system PreControlGrammar.grammar).run
          (PreControlGrammar.acceptedRefinement.boundary (t+duration))).pc ∧
      ((ProducerGrammar.system PreControlGrammar.grammar).run
        (PreControlGrammar.acceptedRefinement.boundary (t+duration))).bank = out ∧
      ZeroReady out ∧ out 18 = 0 ∧ out 16 = 0 ∧
      (∀ j, Protected j → out j = bank j) ∧
      (∀ u, PreControlGrammar.acceptedRefinement.boundary t ≤ u →
        u < PreControlGrammar.acceptedRefinement.boundary (t+duration) →
        ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  obtain ⟨out,d,hd,hseg,hout,hcount,hresult,hframe⟩ :=
    zero_clock_reference_graph branches bank hclock h4 h17 hexpected hbranches
  have hphysical := transfer_silent_graph t d 15 77 bank out hstate hd hseg
  exact ⟨out,d,hd,hphysical.1,hphysical.2.2.1,hphysical.2.2.2.1,hout,hcount,hresult,hframe,hphysical.2.2.2.2⟩

/-- Reference setup preserves the full protected frame when its scratch cells
are zero, including the omitted registers and the unbounded tail. -/
theorem setup_protected (bank : Nat → Nat) (h4 : bank 4 = 0) (h17 : bank 17 = 0)
    (j : Nat) (hj : Protected j) : afterReferenceRaw bank j = bank j := by
  rw [reference_setup_effect bank h4 h17]
  have h16 : j ≠ 16 := by simp only [Protected] at hj; omega
  have h18 : j ≠ 18 := by simp only [Protected] at hj; omega
  simp [h16,h18]

/-- From the actual reference-phase entry, the complete setup and every
reference branch compose into the source reference result. The only open
semantic premise is the displayed bounded-evaluator interface plus its
explicit readiness condition after setup. -/
theorem reference_phase_graph (Ready : (Nat → Nat) → Prop) (E : EvaluationInterface Ready)
    (bank : Nat → Nat) (h4 : bank 4 = 0) (h17 : bank 17 = 0)
    (hready : Ready (afterReferenceRaw bank)) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨6,bank⟩ ⟨77,out⟩ duration ∧
      Ready out ∧ out 18 = 0 ∧
      out 16 = (if Source.reference (bank 13) (bank 14) (bank 15) then 1 else 0) ∧
      (∀ j, Protected j → out j = bank j) := by
  let prepared := afterReferenceRaw bank
  have h13 : prepared 13 = bank 13 := setup_protected bank h4 h17 13 (by unfold Protected; omega)
  have h14 : prepared 14 = bank 14 := setup_protected bank h4 h17 14 (by unfold Protected; omega)
  have h15 : prepared 15 = bank 15 := setup_protected bank h4 h17 15 (by unfold Protected; omega)
  have h16 : prepared 16 = 0 := by simp [prepared,afterReferenceRaw]
  have h18 : prepared 18 = bank 14 := by simp [prepared,afterReferenceRaw,h17]
  obtain ⟨out,d,hd,hsearch,hout,hcount,hresult,hframe⟩ :=
    reference_search_graph Ready E (bank 14) prepared hready h16 h18
  have hsetup := reference_setup_raw bank
  have hq := silent_trans originalRows _ _ _ _ _ hsetup hsearch
  refine ⟨out,setupTime bank+d,by omega,hq,hout,hcount,?_,?_⟩
  · rw [hresult,h14,h15,h13]
    rfl
  · intro j hj
    exact (hframe j hj).trans (setup_protected bank h4 h17 j hj)

/-- The full conditional reference phase, including its exact final grammar
configuration and preservation of every protected register. -/
theorem reference_phase_to_grammar (Ready : (Nat → Nat) → Prop) (E : EvaluationInterface Ready)
    (t : Nat) (bank : Nat → Nat) (hstate : (system originalRows).run t = ⟨6,bank⟩)
    (h4 : bank 4 = 0) (h17 : bank 17 = 0) (hready : Ready (afterReferenceRaw bank)) :
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
      Ready out ∧ out 18 = 0 ∧
      out 16 = (if Source.reference (bank 13) (bank 14) (bank 15) then 1 else 0) ∧
      (∀ j, Protected j → out j = bank j) ∧
      (∀ u, PreControlGrammar.acceptedRefinement.boundary t ≤ u →
        u < PreControlGrammar.acceptedRefinement.boundary (t+duration) →
        ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  obtain ⟨out,d,hd,hseg,hout,hcount,hresult,hframe⟩ := reference_phase_graph Ready E bank h4 h17 hready
  have hphysical := transfer_silent_graph t d 6 77 bank out hstate hd hseg
  exact ⟨out,d,hd,hphysical.1,hphysical.2.1,hphysical.2.2.1,hphysical.2.2.2.1,
    hout,hcount,hresult,hframe,hphysical.2.2.2.2⟩

/-- With zero reference clock, the entire reference phase is unconditional
apart from the two explicit scratch-zero entry conditions. -/
theorem zero_clock_reference_phase_graph (bank : Nat → Nat)
    (hclock : bank 13 = 0) (h4 : bank 4 = 0) (h17 : bank 17 = 0) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨6,bank⟩ ⟨77,out⟩ duration ∧
      ZeroReady out ∧ out 18 = 0 ∧ out 16 = 0 ∧
      (∀ j, Protected j → out j = bank j) := by
  have hready : ZeroReady (afterReferenceRaw bank) := by
    simp [ZeroReady,afterReferenceRaw,hclock]
  obtain ⟨out,d,hd,hseg,hout,hcount,hresult,hframe⟩ :=
    reference_phase_graph ZeroReady zero_evaluation_interface bank h4 h17 hready
  refine ⟨out,d,hd,hseg,hout,hcount,?_,hframe⟩
  simpa [Source.reference,hclock] using hresult

/-- Zero-clock reference evaluation from the actual row-6 phase entry to the
checked grammar's row-77 boundary, with no hidden evaluator premise. -/
theorem zero_clock_reference_phase_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨6,bank⟩)
    (hclock : bank 13 = 0) (h4 : bank 4 = 0) (h17 : bank 17 = 0) :
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
      ZeroReady out ∧ out 18 = 0 ∧ out 16 = 0 ∧
      (∀ j, Protected j → out j = bank j) ∧
      (∀ u, PreControlGrammar.acceptedRefinement.boundary t ≤ u →
        u < PreControlGrammar.acceptedRefinement.boundary (t+duration) →
        ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  have hready : ZeroReady (afterReferenceRaw bank) := by
    simp [ZeroReady,afterReferenceRaw,hclock]
  obtain ⟨out,d,hd,hpos,hbound,hpc,hbank,hout,hcount,hresult,hframe,hquiet⟩ :=
    reference_phase_to_grammar ZeroReady zero_evaluation_interface t bank hstate h4 h17 hready
  have hzero : out 16 = 0 := by simpa [Source.reference,hclock] using hresult
  exact ⟨out,d,hd,hpos,hbound,hpc,hbank,hout,hcount,hzero,hframe,hquiet⟩

end Shared.PNP.Record285.SourceReferenceSearch
