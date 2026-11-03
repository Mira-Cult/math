import Shared.PNP.Record285.SourceReferenceStart

/-! The reference evaluator's branch-entry block. Both branch outcomes and
the full register bank are explicit; zero-scratch invariants remain premises
for interpreting arbitrary entries as source assignments. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SourceReferenceBranch
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin
open Shared.PNP.Record285.SourceReferenceStart

def afterBranchReset (bank : Nat → Nat) : Nat → Nat :=
  clear 3 (clear 2 (clear 19 (update (.dec 18) bank)))

def afterStepsCopy (bank : Nat → Nat) : Nat → Nat :=
  copyRaw 13 17 4 20 (afterBranchReset bank)

def afterBranchRaw (bank : Nat → Nat) : Nat → Nat :=
  copyRaw 18 17 4 0 (afterStepsCopy bank)

def branchTime (bank : Nat → Nat) : Nat :=
  1 + (bank 19+1) + (bank 2+1) + (bank 3+1) +
  copyTime 13 17 4 20 (afterBranchReset bank) +
  copyTime 18 17 4 0 (afterStepsCopy bank)

/-- A zero branch counter exits the reference search immediately and silently. -/
theorem zero_branch (bank : Nat → Nat) (hz : bank 18 = 0) :
    Silent originalRows ⟨15,bank⟩ ⟨77,bank⟩ 1 := by
  have hdec := dec_at_zero 18 bank hz
  apply silent_one originalRows
  simp [step,originalRows,observe,hz,hdec]

/-- A positive branch counter executes the complete branch setup and reaches
the evaluator's step test. All input banks and overwritten destinations are
permitted; only the selected control outcome requires positivity. -/
theorem positive_branch_raw (bank : Nat → Nat) (hp : 0 < bank 18) :
    Silent originalRows ⟨15,bank⟩ ⟨35,afterBranchRaw bank⟩ (branchTime bank) := by
  let k1 := update (.dec 18) bank
  let k2 := clear 19 k1
  let k3 := clear 2 k2
  let k4 := clear 3 k3
  let k5 := copyRaw 13 17 4 20 k4
  let k6 := copyRaw 18 17 4 0 k5
  have hn : bank 18 ≠ 0 := by omega
  have hfirst : step originalRows ⟨15,bank⟩ = (⟨16,k1⟩,false) := by
    simp [step,originalRows,observe,hn,k1]
  have h0 : Silent originalRows ⟨15,bank⟩ ⟨16,k1⟩ 1 := silent_one _ _ _ hfirst
  have hr16 : originalRows[16]? = some ⟨.dec 19,16,17⟩ := by decide
  have hr17 : originalRows[17]? = some ⟨.dec 2,17,18⟩ := by decide
  have hr18 : originalRows[18]? = some ⟨.dec 3,18,19⟩ := by decide
  have hv19 : k1 19 = bank 19 := by simp [k1,update]
  have h1 : Silent originalRows ⟨16,k1⟩ ⟨17,k2⟩ (bank 19+1) :=
    clear_run _ 16 17 19 (bank 19) k1 hr16 hv19
  have hv2 : k2 2 = bank 2 := by simp [k2,k1,clear,update]
  have h2 : Silent originalRows ⟨17,k2⟩ ⟨18,k3⟩ (bank 2+1) :=
    clear_run _ 17 18 2 (bank 2) k2 hr17 hv2
  have hv3 : k3 3 = bank 3 := by simp [k3,k2,k1,clear,update]
  have h3 : Silent originalRows ⟨18,k3⟩ ⟨19,k4⟩ (bank 3+1) :=
    clear_run _ 18 19 3 (bank 3) k3 hr18 hv3
  have hr19 : originalRows[19]? = some ⟨.dec 13,20,22⟩ := by decide
  have hr20 : originalRows[20]? = some ⟨.inc 17,21,21⟩ := by decide
  have hr21 : originalRows[21]? = some ⟨.inc 4,19,19⟩ := by decide
  have hr22 : originalRows[22]? = some ⟨.dec 4,23,24⟩ := by decide
  have hr23 : originalRows[23]? = some ⟨.inc 13,22,22⟩ := by decide
  have hr24 : originalRows[24]? = some ⟨.dec 20,24,25⟩ := by decide
  have hr25 : originalRows[25]? = some ⟨.dec 17,26,27⟩ := by decide
  have hr26 : originalRows[26]? = some ⟨.inc 20,25,25⟩ := by decide
  have h4 : Silent originalRows ⟨19,k4⟩ ⟨27,k5⟩ (copyTime 13 17 4 20 k4) :=
    copy_block originalRows 19 20 21 22 23 24 25 26 27 13 17 4 20 k4
      hr19 hr20 hr21 hr22 hr23 hr24 hr25 hr26
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hr27 : originalRows[27]? = some ⟨.dec 18,28,30⟩ := by decide
  have hr28 : originalRows[28]? = some ⟨.inc 17,29,29⟩ := by decide
  have hr29 : originalRows[29]? = some ⟨.inc 4,27,27⟩ := by decide
  have hr30 : originalRows[30]? = some ⟨.dec 4,31,32⟩ := by decide
  have hr31 : originalRows[31]? = some ⟨.inc 18,30,30⟩ := by decide
  have hr32 : originalRows[32]? = some ⟨.dec 0,32,33⟩ := by decide
  have hr33 : originalRows[33]? = some ⟨.dec 17,34,35⟩ := by decide
  have hr34 : originalRows[34]? = some ⟨.inc 0,33,33⟩ := by decide
  have h5 : Silent originalRows ⟨27,k5⟩ ⟨35,k6⟩ (copyTime 18 17 4 0 k5) :=
    copy_block originalRows 27 28 29 30 31 32 33 34 35 18 17 4 0 k5
      hr27 hr28 hr29 hr30 hr31 hr32 hr33 hr34
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hq := silent_trans originalRows _ _ _ _ _ h0 h1
  have hq := silent_trans originalRows _ _ _ _ _ hq h2
  have hq := silent_trans originalRows _ _ _ _ _ hq h3
  have hq := silent_trans originalRows _ _ _ _ _ hq h4
  have hq := silent_trans originalRows _ _ _ _ _ hq h5
  change Silent originalRows ⟨15,bank⟩ ⟨35,k6⟩ (branchTime bank)
  change Silent originalRows ⟨15,bank⟩ ⟨35,k6⟩
    (1+(bank 19+1)+(bank 2+1)+(bank 3+1)+copyTime 13 17 4 20 k4+copyTime 18 17 4 0 k5)
  exact hq

/-- The complete raw effect exposes nonzero scratch rather than discarding it. -/
def branchView (bank : Nat → Nat) : Nat → Nat := fun j =>
  if j = 2 then 0 else if j = 3 then 0 else if j = 4 then 0
  else if j = 17 then 0 else if j = 19 then 0
  else if j = 13 then bank 4 + bank 13
  else if j = 20 then bank 17 + bank 13
  else if j = 18 then bank 18-1 else if j = 0 then bank 18-1
  else bank j

theorem afterBranchRaw_view (bank : Nat → Nat) : afterBranchRaw bank = branchView bank := by
  funext j
  by_cases h2 : j = 2
  · subst j; simp [afterBranchRaw,afterStepsCopy,afterBranchReset,copyRaw,splitResult,clear,update,branchView]
  · by_cases h3 : j = 3
    · subst j; simp [afterBranchRaw,afterStepsCopy,afterBranchReset,copyRaw,splitResult,clear,update,branchView]
    · by_cases h4 : j = 4
      · subst j; simp [afterBranchRaw,copyRaw,clear,update,branchView]
      · by_cases h17 : j = 17
        · subst j; simp [afterBranchRaw,copyRaw,update,branchView]
        · by_cases h19 : j = 19
          · subst j; simp [afterBranchRaw,afterStepsCopy,afterBranchReset,copyRaw,splitResult,clear,update,branchView]
          · by_cases h13 : j = 13
            · subst j; simp [afterBranchRaw,afterStepsCopy,afterBranchReset,copyRaw,splitResult,clear,update,branchView]
            · by_cases h20 : j = 20
              · subst j; simp [afterBranchRaw,afterStepsCopy,afterBranchReset,copyRaw,splitResult,clear,update,branchView]
              · by_cases h18 : j = 18
                · subst j; simp [afterBranchRaw,afterStepsCopy,afterBranchReset,copyRaw,splitResult,clear,update,branchView]
                · by_cases h0 : j = 0
                  · subst j; simp [afterBranchRaw,afterStepsCopy,afterBranchReset,copyRaw,splitResult,clear,update,branchView]
                  · simp [afterBranchRaw,afterStepsCopy,afterBranchReset,copyRaw,splitResult,clear,update,branchView,
                      h2,h3,h4,h17,h19,h13,h20,h18,h0]

theorem branchTime_formula (bank : Nat → Nat) :
    branchTime bank = bank 19 + bank 2 + bank 3 + bank 20 + bank 0 +
      7*bank 13 + 2*bank 4 + 2*bank 17 + 7*(bank 18-1) + 12 := by
  simp [branchTime,copyTime,afterStepsCopy,afterBranchReset,copyRaw,splitResult,clear,update]
  omega

/-- Under the explicit scratch invariant, this is the source assignment:
`branches -= 1; left = right = state = 0; steps = n; choices = branches`. -/
theorem branch_source_fields (bank : Nat → Nat) (h4 : bank 4 = 0) (h17 : bank 17 = 0) :
    let b := afterBranchRaw bank
    b 18 = bank 18-1 ∧ b 19 = 0 ∧ b 2 = 0 ∧ b 3 = 0 ∧
    b 20 = bank 13 ∧ b 0 = bank 18-1 ∧ b 13 = bank 13 ∧
    b 4 = 0 ∧ b 17 = 0 := by
  rw [afterBranchRaw_view]
  simp [branchView,h4,h17]

/-- Nonzero scratch can change both the source length and the copied clock. -/
theorem branch_scratch_necessary (bank : Nat → Nat) :
    (afterBranchRaw bank 13 = bank 13 ↔ bank 4 = 0) ∧
    (afterBranchRaw bank 20 = bank 13 ↔ bank 17 = 0) := by
  rw [afterBranchRaw_view]
  simp [branchView]

/-- Frame slots of the selected pre-control grammar used by this evaluator
boundary. The compiler's source-allocation correspondence remains open. -/
theorem branch_slots_named :
    PreControlGrammar.grammar.names[19]? = some "$liveframe.0.7" ∧
    PreControlGrammar.grammar.names[2]? = some "$liveframe.0.8" ∧
    PreControlGrammar.grammar.names[3]? = some "$liveframe.0.9" ∧
    PreControlGrammar.grammar.names[20]? = some "$liveframe.0.10" ∧
    PreControlGrammar.grammar.names[0]? = some "$liveframe.0.11" := by decide

def referenceSimState (bank : Nat → Nat) : Source.SimState :=
  ⟨bank 19,bank 2,bank 3,bank 0⟩

/-- With clean scratch, the complete branch-entry state agrees with the
bounded reference evaluator's initial virtual tape and choice stream. -/
theorem branch_matches_reference (bank : Nat → Nat) (h4 : bank 4 = 0) (h17 : bank 17 = 0) :
    referenceSimState (afterBranchRaw bank) = ⟨0,0,0,bank 18-1⟩ ∧
    (afterBranchRaw bank) 20 = bank 13 ∧
    sourceState (afterBranchRaw bank) .compare = sourceState bank .compare := by
  rw [afterBranchRaw_view]
  simp [referenceSimState,branchView,sourceState,h4,h17]

/-- Any positive silent graph segment transfers to a finite silent grammar
segment with the exact destination occurrence and entire resulting bank. -/
theorem transfer_silent_graph (t duration pc exit : Nat) (bank result : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨pc,bank⟩)
    (hpos : 0 < duration)
    (hseg : Silent originalRows ⟨pc,bank⟩ ⟨exit,result⟩ duration) :
    let r := PreControlGrammar.acceptedRefinement
    let g := (ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary (t+duration))
    r.boundary t < r.boundary (t+duration) ∧
    r.boundary (t+duration) ≤ r.boundary t + 32*duration ∧
    PreControlGrammar.positions[exit]? = some g.pc ∧ g.bank = result ∧
    (∀ u, r.boundary t ≤ u → u < r.boundary (t+duration) →
      ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  dsimp only
  let r := PreControlGrammar.acceptedRefinement
  have hend : (system originalRows).run (t+duration) = ⟨exit,result⟩ := by
    rw [EventSystem.run_add,hstate]
    exact hseg.1
  have hrel := r.related (t+duration)
  change ProducerGrammar.Rel originalRows PreControlGrammar.positions _ _ at hrel
  rw [hend] at hrel
  have hquiet : ∀ i, t ≤ i → i < t+duration → ¬ (system originalRows).BeepAt i := by
    intro i hlo hhi hb
    have heq : i = t+(i-t) := by omega
    have hb' : (system originalRows).BeepFrom ⟨pc,bank⟩ (i-t) := by
      rw [heq] at hb
      have ht := ((system originalRows).beepAt_add_iff t (i-t)).1 hb
      simpa [hstate] using ht
    exact hseg.2 (i-t) (by omega) hb'
  exact ⟨r.boundary_strict (by omega),grammar_boundary_bound t duration,hrel.1,hrel.2.1.symm,
    silent_interval_transfer r t duration hquiet⟩

theorem positive_branch_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨15,bank⟩) (hp : 0 < bank 18) :
    let r := PreControlGrammar.acceptedRefinement
    let g := (ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary (t+branchTime bank))
    r.boundary t < r.boundary (t+branchTime bank) ∧
    r.boundary (t+branchTime bank) ≤ r.boundary t + 32*branchTime bank ∧
    PreControlGrammar.positions[35]? = some g.pc ∧ g.bank = afterBranchRaw bank ∧
    (∀ u, r.boundary t ≤ u → u < r.boundary (t+branchTime bank) →
      ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  have hpTime : 0 < branchTime bank := by simp only [branchTime]; omega
  exact transfer_silent_graph t (branchTime bank) 15 35 bank (afterBranchRaw bank)
    hstate hpTime (positive_branch_raw bank hp)

/-- At a reachable positive branch with clean scratch, the grammar reaches
the exact virtual evaluator input and emits no event during preparation. -/
theorem positive_branch_matches_reference (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨15,bank⟩) (hp : 0 < bank 18)
    (h4 : bank 4 = 0) (h17 : bank 17 = 0) :
    let r := PreControlGrammar.acceptedRefinement
    let g := (ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary (t+branchTime bank))
    r.boundary t < r.boundary (t+branchTime bank) ∧
    r.boundary (t+branchTime bank) ≤ r.boundary t + 32*branchTime bank ∧
    PreControlGrammar.positions[35]? = some g.pc ∧
    referenceSimState g.bank = ⟨0,0,0,bank 18-1⟩ ∧ g.bank 20 = bank 13 ∧
    sourceState g.bank .compare = sourceState bank .compare ∧
    (∀ u, r.boundary t ≤ u → u < r.boundary (t+branchTime bank) →
      ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  dsimp only
  have h := positive_branch_to_grammar t bank hstate hp
  have hm := branch_matches_reference bank h4 h17
  rw [h.2.2.2.1]
  exact ⟨h.1,h.2.1,h.2.2.1,hm.1,hm.2.1,hm.2.2,h.2.2.2.2⟩

theorem zero_branch_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨15,bank⟩) (hz : bank 18 = 0) :
    let r := PreControlGrammar.acceptedRefinement
    let g := (ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary (t+1))
    r.boundary t < r.boundary (t+1) ∧ r.boundary (t+1) ≤ r.boundary t + 32 ∧
    PreControlGrammar.positions[77]? = some g.pc ∧ g.bank = bank ∧
    (∀ u, r.boundary t ≤ u → u < r.boundary (t+1) →
      ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  simpa using transfer_silent_graph t 1 15 77 bank bank hstate (by decide) (zero_branch bank hz)

/-- The bank at the first reference branch, reached from the all-zero entry. -/
def firstBranchBank : Nat → Nat := afterReferenceRaw (afterBegin firstBank)

theorem first_branch_graph : (system originalRows).run 18 = ⟨15,firstBranchBank⟩ := by
  have h := reference_setup_raw (afterBegin firstBank)
  have htime : setupTime (afterBegin firstBank) = 12 := by
    simp [setupTime,afterBegin,firstBank,clear,update]
  rw [htime] at h
  have he : 18 = 6+12 := by decide
  rw [he,EventSystem.run_add,first_setup_graph]
  exact h.1

theorem first_branch_values :
    firstBranchBank 18 = 1 ∧ firstBranchBank 13 = 0 ∧
    firstBranchBank 4 = 0 ∧ firstBranchBank 17 = 0 ∧
    firstBranchBank 16 = 0 := by
  simp [firstBranchBank,afterReferenceRaw,afterBegin,firstBank,clear,update]

theorem first_branch_time : branchTime firstBranchBank = 12 := by
  rw [branchTime_formula]
  simp [firstBranchBank,afterReferenceRaw,afterBegin,firstBank,clear,update]

def firstEvaluatorBank : Nat → Nat := afterBranchRaw firstBranchBank

theorem first_evaluator_values :
    firstEvaluatorBank 20 = 0 ∧ firstEvaluatorBank 18 = 0 ∧
    firstEvaluatorBank 16 = 0 ∧ firstEvaluatorBank 4 = 0 ∧ firstEvaluatorBank 17 = 0 := by
  rw [firstEvaluatorBank,afterBranchRaw_view]
  simp [branchView,firstBranchBank,afterReferenceRaw,afterBegin,firstBank,clear,update]

/-- The first branch has zero clock; the step and branch tests then exit the
reference search in two further silent graph transitions. -/
theorem first_reference_graph_segment :
    Silent originalRows ⟨15,firstBranchBank⟩ ⟨77,firstEvaluatorBank⟩ 14 := by
  have hp : 0 < firstBranchBank 18 := by rw [first_branch_values.1]; decide
  have hbranch := positive_branch_raw firstBranchBank hp
  rw [first_branch_time] at hbranch
  change Silent originalRows ⟨15,firstBranchBank⟩ ⟨35,firstEvaluatorBank⟩ 12 at hbranch
  have hsteps : firstEvaluatorBank 20 = 0 := first_evaluator_values.1
  have hbranches : firstEvaluatorBank 18 = 0 := first_evaluator_values.2.1
  have hd20 := dec_at_zero 20 firstEvaluatorBank hsteps
  have hd18 := dec_at_zero 18 firstEvaluatorBank hbranches
  have h35 : step originalRows ⟨35,firstEvaluatorBank⟩ = (⟨15,firstEvaluatorBank⟩,false) := by
    simp [step,originalRows,observe,hsteps,hd20]
  have h15 : step originalRows ⟨15,firstEvaluatorBank⟩ = (⟨77,firstEvaluatorBank⟩,false) := by
    simp [step,originalRows,observe,hbranches,hd18]
  have hlast := silent_trans originalRows _ _ _ 1 1 (silent_one _ _ _ h35) (silent_one _ _ _ h15)
  have h := silent_trans originalRows _ _ _ 12 2 hbranch hlast
  simpa using h

theorem first_reference_graph_finish : (system originalRows).run 32 = ⟨77,firstEvaluatorBank⟩ := by
  have he : 32 = 18+14 := by decide
  rw [he,EventSystem.run_add,first_branch_graph]
  exact first_reference_graph_segment.1

/-- The first reference phase completes with the exact zero-clock reference
answer and a fully specified bank at the checked grammar boundary. -/
theorem first_reference_complete :
    let r := PreControlGrammar.acceptedRefinement
    let g := (ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary 32)
    PreControlGrammar.positions[77]? = some g.pc ∧ g.bank = firstEvaluatorBank ∧
    g.bank 16 = (if Source.reference 0 1 0 then 1 else 0) ∧
    (∀ u, r.boundary 18 ≤ u → u < r.boundary 32 →
      ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  have h := transfer_silent_graph 18 14 15 77 firstBranchBank firstEvaluatorBank
    first_branch_graph (by decide) first_reference_graph_segment
  simp only [Nat.reduceAdd] at h
  have href : Source.reference 0 1 0 = false := by simp [Source.reference]
  dsimp only
  refine ⟨h.2.2.1,h.2.2.2.1,?_,h.2.2.2.2⟩
  rw [h.2.2.2.1,href]
  exact first_evaluator_values.2.2.1

/-- From the all-zero entry through the completed first reference search, the
checked grammar has exactly one event. -/
theorem first_reference_complete_unique_event :
    let r := PreControlGrammar.acceptedRefinement
    ∃ event, (event < r.boundary 32 ∧ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt event) ∧
      ∀ other, (other < r.boundary 32 ∧ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt other) → other = event := by
  dsimp only
  let r := PreControlGrammar.acceptedRefinement
  have hfirst := first_reference_unique_event
  have hcomplete := first_reference_complete
  have hbound : r.boundary 18 ≤ r.boundary 32 := r.boundary_mono (by decide)
  dsimp only [r] at hbound
  obtain ⟨event,hevent,hunique⟩ := hfirst
  refine ⟨event,⟨by omega,hevent.2⟩,?_⟩
  intro other hother
  by_cases hbefore : other < PreControlGrammar.acceptedRefinement.boundary 18
  · exact hunique other ⟨hbefore,hother.2⟩
  · have hq := hcomplete.2.2.2
    exact False.elim (hq other (by omega) hother.1 hother.2)

end Shared.PNP.Record285.SourceReferenceBranch
