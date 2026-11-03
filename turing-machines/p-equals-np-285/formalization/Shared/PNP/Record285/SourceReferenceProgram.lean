import Shared.PNP.Record285.SourceChoiceStep
import Shared.PNP.Record285.OwnershipExpandedLoop

/-! The positive-clock reference evaluator's program-value preparation. It
implements `digit := radix + remaining` when its two scratch slots are zero;
its exact raw semantics also exposes nonzero scratch. Record decoding and the
virtual transition are still separate obligations. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SourceReferenceProgram
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin
open Shared.PNP.Record285.SourceReferenceStart
open Shared.PNP.Record285.SourceReferenceBranch
open Shared.PNP.Record285.SourceChoiceStep

def afterProgramRaw (bank : Nat → Nat) : Nat → Nat := fun j =>
  if j = 4 then 0 else if j = 5 then 0
  else if j = 14 then bank 4 + bank 14
  else if j = 1 then bank 5 + bank 14 + bank 15 else bank j

def programTime (bank : Nat → Nat) : Nat :=
  7*bank 14 + 7*bank 15 + 2*bank 4 + 2*bank 5 + bank 1 + 6

/-- The actual 38--50 graph block terminates silently for arbitrary register
contents, with the exact full-bank result and exact graph duration. -/
theorem reference_program_raw (bank : Nat → Nat) :
    Silent originalRows ⟨38,bank⟩ ⟨51,afterProgramRaw bank⟩ (programTime bank) := by
  let k1 := splitResult 14 5 4 bank
  let k2 := update (.move 4 14) k1
  let k3 := splitResult 15 5 4 k2
  let k4 := update (.move 4 15) k3
  let k5 := clear 1 k4
  let k6 := update (.move 5 1) k5
  have hr38 : originalRows[38]? = some ⟨.dec 14,39,41⟩ := by decide
  have hr39 : originalRows[39]? = some ⟨.inc 5,40,40⟩ := by decide
  have hr40 : originalRows[40]? = some ⟨.inc 4,38,38⟩ := by decide
  have hr41 : originalRows[41]? = some ⟨.dec 4,42,43⟩ := by decide
  have hr42 : originalRows[42]? = some ⟨.inc 14,41,41⟩ := by decide
  have hr43 : originalRows[43]? = some ⟨.dec 15,44,46⟩ := by decide
  have hr44 : originalRows[44]? = some ⟨.inc 5,45,45⟩ := by decide
  have hr45 : originalRows[45]? = some ⟨.inc 4,43,43⟩ := by decide
  have hr46 : originalRows[46]? = some ⟨.dec 4,47,48⟩ := by decide
  have hr47 : originalRows[47]? = some ⟨.inc 15,46,46⟩ := by decide
  have hr48 : originalRows[48]? = some ⟨.dec 1,48,49⟩ := by decide
  have hr49 : originalRows[49]? = some ⟨.dec 5,50,51⟩ := by decide
  have hr50 : originalRows[50]? = some ⟨.inc 1,49,49⟩ := by decide
  have hs1 : Silent originalRows ⟨38,bank⟩ ⟨41,k1⟩ (3*bank 14+1) :=
    split_run _ 38 39 40 41 14 5 4 (bank 14) bank hr38 hr39 hr40
      (by decide) (by decide) (by decide) rfl
  have haux1 : k1 4 = bank 4 + bank 14 := by simp [k1,splitResult]
  have hm1 : Silent originalRows ⟨41,k1⟩ ⟨43,k2⟩ (2*(bank 4+bank 14)+1) :=
    expanded_move_run _ 41 42 43 4 14 (bank 4+bank 14) k1 hr41 hr42 (by decide) haux1
  have hsrc2 : k2 15 = bank 15 := by simp [k2,k1,update,splitResult]
  have hs2 : Silent originalRows ⟨43,k2⟩ ⟨46,k3⟩ (3*bank 15+1) :=
    split_run _ 43 44 45 46 15 5 4 (bank 15) k2 hr43 hr44 hr45
      (by decide) (by decide) (by decide) hsrc2
  have haux2 : k3 4 = bank 15 := by simp [k3,k2,k1,splitResult,update]
  have hm2 : Silent originalRows ⟨46,k3⟩ ⟨48,k4⟩ (2*bank 15+1) :=
    expanded_move_run _ 46 47 48 4 15 (bank 15) k3 hr46 hr47 (by decide) haux2
  have hdst : k4 1 = bank 1 := by simp [k4,k3,k2,k1,update,splitResult]
  have hc : Silent originalRows ⟨48,k4⟩ ⟨49,k5⟩ (bank 1+1) :=
    clear_run _ 48 49 1 (bank 1) k4 hr48 hdst
  have htemp : k5 5 = bank 5 + bank 14 + bank 15 := by
    simp [k5,k4,k3,k2,k1,clear,update,splitResult]
  have hm3 : Silent originalRows ⟨49,k5⟩ ⟨51,k6⟩ (2*(bank 5+bank 14+bank 15)+1) :=
    expanded_move_run _ 49 50 51 5 1 (bank 5+bank 14+bank 15) k5 hr49 hr50 (by decide) htemp
  have hq := silent_trans originalRows _ _ _ _ _ hs1 hm1
  have hq := silent_trans originalRows _ _ _ _ _ hq hs2
  have hq := silent_trans originalRows _ _ _ _ _ hq hm2
  have hq := silent_trans originalRows _ _ _ _ _ hq hc
  have hq := silent_trans originalRows _ _ _ _ _ hq hm3
  have heffect : k6 = afterProgramRaw bank := by
    funext j
    by_cases h4 : j = 4
    · subst j; simp [k6,k5,k4,k3,k2,k1,update,clear,afterProgramRaw]
    · by_cases h5 : j = 5
      · subst j; simp [k6,k5,k4,k3,k2,k1,update,afterProgramRaw]
      · by_cases h14 : j = 14
        · subst j; simp [k6,k5,k4,k3,k2,k1,update,splitResult,clear,afterProgramRaw]
        · by_cases h1 : j = 1
          · subst j; simp [k6,k5,k4,k3,k2,k1,update,splitResult,clear,afterProgramRaw]
          · by_cases h15 : j = 15
            · subst j; simp [k6,k5,k4,k3,k2,k1,update,splitResult,clear,afterProgramRaw]
            · simp [k6,k5,k4,k3,k2,k1,update,splitResult,clear,afterProgramRaw,h4,h5,h14,h1,h15]
  have htime : programTime bank = (3*bank 14+1)+(2*(bank 4+bank 14)+1)+
      (3*bank 15+1)+(2*bank 15+1)+(bank 1+1)+(2*(bank 5+bank 14+bank 15)+1) := by
    simp only [programTime]; omega
  rw [htime,← heffect]
  exact hq

/-- Both scratch-zero conditions are necessary for the corresponding source
values, not just convenient assumptions for the proof. -/
theorem program_scratch_necessary (bank : Nat → Nat) :
    (afterProgramRaw bank 14 = bank 14 ↔ bank 4 = 0) ∧
    (afterProgramRaw bank 1 = bank 14+bank 15 ↔ bank 5 = 0) := by
  simp [afterProgramRaw]

/-- Clean scratch yields the intended program sum and preserves the full
unbounded frame. -/
theorem reference_program_clean (bank : Nat → Nat) (h4 : bank 4 = 0) (h5 : bank 5 = 0) :
    afterProgramRaw bank = (fun j => if j = 1 then bank 14+bank 15 else bank j) := by
  funext j
  by_cases hj4 : j = 4
  · subst j; simp [afterProgramRaw,h4]
  · by_cases hj5 : j = 5
    · subst j; simp [afterProgramRaw,h5]
    · by_cases hj14 : j = 14
      · subst j; simp [afterProgramRaw,h4]
      · by_cases hj1 : j = 1
        · subst j; simp [afterProgramRaw,h5]
        · simp [afterProgramRaw,hj4,hj5,hj14,hj1]

/-- For clean scratch, the composition computes the exact source selector,
remaining choice stream, clock, and reference program while preserving every
other register. -/
theorem prepared_matches_source (bank : Nat → Nat) (h4 : bank 4 = 0) (h5 : bank 5 = 0) :
    let out := afterProgramRaw (choiceBank bank)
    out 1 = bank 14 + bank 15 ∧
    out 3 = (referenceSimState bank).selector + (referenceSimState bank).choices%2 ∧
    out 0 = (referenceSimState bank).choices/2 ∧ out 20 = bank 20-1 ∧
    (∀ j, j ≠ 1 → j ≠ 3 → j ≠ 0 → j ≠ 20 → out j = bank j) := by
  have hc4 : choiceBank bank 4 = 0 := by
    have h := choiceBank_read bank 4
    simpa [h4] using h
  have hc5 : choiceBank bank 5 = 0 := by
    have h := choiceBank_read bank 5
    simpa [h5] using h
  have hc := reference_program_clean (choiceBank bank) hc4 hc5
  dsimp only
  rw [hc]
  refine ⟨?_,?_,?_,?_,?_⟩
  · have h14 : choiceBank bank 14 = bank 14 := by simpa using choiceBank_read bank 14
    have h15 : choiceBank bank 15 = bank 15 := by simpa using choiceBank_read bank 15
    simp [h14,h15]
  · have h := choiceBank_read bank 3
    simpa [referenceSimState] using h
  · have h := choiceBank_read bank 0
    simpa [referenceSimState] using h
  · have h := choiceBank_read bank 20
    simpa using h
  · intro j h1 h3 h0 h20
    simp only [if_neg h1]
    have h := choiceBank_read bank j
    simpa [h20,h0,h3] using h

/-- The whole checked graph prefix from the step test to program decoding,
with exact full-bank effect and strictly positive duration. -/
theorem reference_prepare_raw (bank : Nat → Nat) (hp : 0 < bank 20) :
    Silent originalRows ⟨35,bank⟩ ⟨51,afterProgramRaw (choiceBank bank)⟩
      (choiceTime bank + programTime (choiceBank bank)) :=
  silent_trans originalRows _ _ _ _ _ (choice_prefix bank hp) (reference_program_raw (choiceBank bank))

/-- The graph prefix transfers to a finite silent run of the exact checked
grammar, with the complete resulting bank and program-decoder occurrence. -/
theorem reference_prepare_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨35,bank⟩) (hp : 0 < bank 20) :
    let d := choiceTime bank + programTime (choiceBank bank)
    let r := PreControlGrammar.acceptedRefinement
    let g := (ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary (t+d))
    r.boundary t < r.boundary (t+d) ∧ r.boundary (t+d) ≤ r.boundary t + 32*d ∧
    PreControlGrammar.positions[51]? = some g.pc ∧ g.bank = afterProgramRaw (choiceBank bank) ∧
    (∀ u, r.boundary t ≤ u → u < r.boundary (t+d) →
      ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  have hpTime : 0 < choiceTime bank + programTime (choiceBank bank) := by
    unfold choiceTime; split <;> omega
  exact transfer_silent_graph t _ 35 51 bank _ hstate hpTime (reference_prepare_raw bank hp)

/-- Under the explicit clean-scratch conditions, the checked grammar reaches
the exact source program, selector, remaining choices, and decremented clock. -/
theorem reference_prepare_matches_source (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨35,bank⟩) (hp : 0 < bank 20)
    (h4 : bank 4 = 0) (h5 : bank 5 = 0) :
    let d := choiceTime bank + programTime (choiceBank bank)
    let r := PreControlGrammar.acceptedRefinement
    let g := (ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary (t+d))
    r.boundary t < r.boundary (t+d) ∧ r.boundary (t+d) ≤ r.boundary t + 32*d ∧
    PreControlGrammar.positions[51]? = some g.pc ∧
    g.bank 1 = bank 14+bank 15 ∧
    g.bank 3 = (referenceSimState bank).selector + (referenceSimState bank).choices%2 ∧
    g.bank 0 = (referenceSimState bank).choices/2 ∧ g.bank 20 = bank 20-1 ∧
    (∀ j, j ≠ 1 → j ≠ 3 → j ≠ 0 → j ≠ 20 → g.bank j = bank j) ∧
    (∀ u, r.boundary t ≤ u → u < r.boundary (t+d) →
      ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  dsimp only
  have h := reference_prepare_to_grammar t bank hstate hp
  have hm := prepared_matches_source bank h4 h5
  rw [h.2.2.2.1]
  exact ⟨h.1,h.2.1,h.2.2.1,hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1,hm.2.2.2.2,h.2.2.2.2⟩

end Shared.PNP.Record285.SourceReferenceProgram
