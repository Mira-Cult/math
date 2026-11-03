import Shared.PNP.Record285.SourceReferenceSearch

/-! Reduce the bounded reference evaluator to one explicit virtual-step
obligation. This module takes the single-step interface as a premise; the
clock loop, timeout, final-step HALT, protected frame, and event accounting
are proved here. `SourceVirtualStep` proves the concrete instance. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SourceVirtualLoop
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin
open Shared.PNP.Record285.SourceReferenceStart
open Shared.PNP.Record285.SourceReferenceBranch
open Shared.PNP.Record285.SourceReferenceSearch

/-- The precise remaining local contract: one positive-clock iteration has
an exact silent graph segment, implements the virtual transition, retains
the full protected frame, and reestablishes `Ready`. No instance for positive
clocks is asserted in this module. -/
structure SingleStepInterface (Ready : (Nat → Nat) → Prop) : Prop where
  scratch : ∀ bank, Ready bank → bank 4 = 0 ∧ bank 17 = 0
  after_setup : ∀ bank, Ready bank → 0 < bank 18 → Ready (afterBranchRaw bank)
  execute_step : ∀ bank, Ready bank → bank 16 = 0 → 0 < bank 20 →
    ∃ out duration, 0 < duration ∧ Ready out ∧ (∀ j, Protected j → out j = bank j) ∧
      match Source.simStep (bank 14+bank 15) (referenceSimState bank) with
      | none => Silent originalRows ⟨35,bank⟩ ⟨15,out⟩ duration ∧ out 18 = 0 ∧ out 16 = 1
      | some next => Silent originalRows ⟨35,bank⟩ ⟨35,out⟩ duration ∧
          out 20 + 1 = bank 20 ∧ referenceSimState out = next ∧ out 18 = bank 18 ∧ out 16 = 0

/-- Given the explicit single-step interface, every finite clock is exhausted
or halts after finitely many positive silent segments. The result and full
protected frame agree with `Source.haltedWithin` for arbitrary starting virtual
states and banks satisfying `Ready`. -/
theorem evaluate_graph (Ready : (Nat → Nat) → Prop) (V : SingleStepInterface Ready)
    (clock : Nat) (bank : Nat → Nat) (hready : Ready bank)
    (hexpected : bank 16 = 0) (hclock : bank 20 = clock) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨35,bank⟩ ⟨15,out⟩ duration ∧
      Ready out ∧ (∀ j, Protected j → out j = bank j) ∧
      out 18 = (if Source.haltedWithin (bank 14+bank 15) clock (referenceSimState bank) then 0 else bank 18) ∧
      out 16 = (if Source.haltedWithin (bank 14+bank 15) clock (referenceSimState bank) then 1 else 0) := by
  induction clock generalizing bank with
  | zero =>
    have hz : bank 20 = 0 := hclock
    have hdec := dec_at_zero 20 bank hz
    have hstep : step originalRows ⟨35,bank⟩ = (⟨15,bank⟩,false) := by
      simp [step,originalRows,observe,hz,hdec]
    have hs : Silent originalRows ⟨35,bank⟩ ⟨15,bank⟩ 1 := silent_one originalRows _ _ hstep
    refine ⟨bank,1,by decide,hs,hready,?_,?_,?_⟩
    · intro j hj; rfl
    · simp [Source.haltedWithin]
    · simp [Source.haltedWithin,hexpected]
  | succ clock ih =>
    have hp : 0 < bank 20 := by omega
    obtain ⟨mid,d,hd,hmidReady,hframe,htransition⟩ := V.execute_step bank hready hexpected hp
    cases hsim : Source.simStep (bank 14+bank 15) (referenceSimState bank) with
    | none =>
      simp only [hsim] at htransition
      obtain ⟨hseg,hcount,hresult⟩ := htransition
      refine ⟨mid,d,hd,hseg,hmidReady,hframe,?_,?_⟩
      · simpa [Source.haltedWithin,hsim] using hcount
      · simpa [Source.haltedWithin,hsim] using hresult
    | some next =>
      simp only [hsim] at htransition
      obtain ⟨hseg,hmidClock,hmidState,hmidCount,hmidExpected⟩ := htransition
      have hmidClock' : mid 20 = clock := by omega
      obtain ⟨out,e,he,hrest,houtReady,houtFrame,houtCount,houtResult⟩ :=
        ih mid hmidReady hmidExpected hmidClock'
      have hp14 : mid 14 = bank 14 := hframe 14 (by unfold Protected; omega)
      have hp15 : mid 15 = bank 15 := hframe 15 (by unfold Protected; omega)
      have heval : Source.haltedWithin (mid 14+mid 15) clock (referenceSimState mid) =
          Source.haltedWithin (bank 14+bank 15) (clock+1) (referenceSimState bank) := by
        rw [hp14,hp15,hmidState]
        simp [Source.haltedWithin,hsim]
      rw [heval,hmidCount] at houtCount
      rw [heval] at houtResult
      have hcombined := silent_trans originalRows _ _ _ d e hseg hrest
      refine ⟨out,d+e,by omega,hcombined,houtReady,?_,houtCount,houtResult⟩
      intro j hj
      exact (houtFrame j hj).trans (hframe j hj)

/-- A one-step proof suffices for the complete evaluator interface consumed by
the reference-search composition. -/
theorem evaluator_of_single_step (Ready : (Nat → Nat) → Prop) (V : SingleStepInterface Ready) :
    EvaluationInterface Ready where
  scratch := V.scratch
  after_setup := V.after_setup
  execute := by
    intro bank hready hexpected hclock hinit
    obtain ⟨out,d,hd,hseg,hout,hframe,hcount,hresult⟩ :=
      evaluate_graph Ready V (bank 20) bank hready hexpected rfl
    rw [hclock] at hcount hresult
    exact ⟨out,d,hd,hseg,hout,hframe,hcount,hresult⟩

/-- The complete reference phase follows from the displayed local step contract. -/
theorem reference_phase_of_single_step (Ready : (Nat → Nat) → Prop) (V : SingleStepInterface Ready)
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
        ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) :=
  reference_phase_to_grammar Ready (evaluator_of_single_step Ready V) t bank hstate h4 h17 hready

end Shared.PNP.Record285.SourceVirtualLoop
