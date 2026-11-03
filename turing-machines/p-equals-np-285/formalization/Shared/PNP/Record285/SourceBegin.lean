import Shared.PNP.Record285.PreControlEndpoint
import Shared.PNP.Record285.Source

/-! The candidate-begin source operation on the checked 21-register graph.
This proves the beep and all three resets for arbitrary complete banks. It
is one source boundary, not a proof of the bounded evaluators or the full
source-to-grammar translation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SourceBegin
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.Source

/-- Clear one register while retaining every other, including the unbounded tail. -/
def clear (i : Nat) (bank : Nat → Nat) : Nat → Nat :=
  fun j => if j = i then 0 else bank j

theorem clear_after_dec (i : Nat) (bank : Nat → Nat) :
    clear i (update (.dec i) bank) = clear i bank := by
  funext j
  by_cases h : j = i <;> simp [clear,update,h]

theorem clear_at_zero (i : Nat) (bank : Nat → Nat) (h : bank i = 0) :
    clear i bank = bank := by
  funext j
  by_cases hj : j = i
  · subst j; simp [clear,h]
  · simp [clear,hj]

theorem dec_at_zero (i : Nat) (bank : Nat → Nat) (h : bank i = 0) :
    update (.dec i) bank = bank := by
  funext j
  by_cases hj : j = i
  · subst j; simp [update,h]
  · simp [update,hj]

/-- A checked self-decrement loop clears its register, runs for exactly one
more step than its initial value, preserves the full frame, and is silent. -/
theorem clear_run (rows : Array Row) (pc exit reg n : Nat) (bank : Nat → Nat)
    (hrow : rows[pc]? = some ⟨.dec reg,pc,exit⟩) (hval : bank reg = n) :
    (system rows).advance ⟨pc,bank⟩ (n+1) = ⟨exit,clear reg bank⟩ ∧
      ∀ j, j < n+1 → ¬ (system rows).BeepFrom ⟨pc,bank⟩ j := by
  induction n generalizing bank with
  | zero =>
    have hz := dec_at_zero reg bank hval
    have hc := clear_at_zero reg bank hval
    have hs : step rows ⟨pc,bank⟩ = (⟨exit,bank⟩,false) := by
      simp [step,hrow,observe,hval,hz]
    constructor
    · change (step rows ⟨pc,bank⟩).1 = _
      rw [hs,hc]
    · intro j hj
      have hj0 : j = 0 := by omega
      subst j
      change ¬ (step rows ⟨pc,bank⟩).2 = true
      simp [hs]
  | succ n ih =>
    have hp : bank reg ≠ 0 := by omega
    have hs : step rows ⟨pc,bank⟩ = (⟨pc,update (.dec reg) bank⟩,false) := by
      simp [step,hrow,observe,hp]
    have hnext : update (.dec reg) bank reg = n := by simp [update]; omega
    obtain ⟨hr,hq⟩ := ih (update (.dec reg) bank) hnext
    have heq : n+1+1 = 1+(n+1) := by omega
    constructor
    · rw [heq,advance_add]
      change (system rows).advance (step rows ⟨pc,bank⟩).1 (n+1) = _
      rw [hs,hr,clear_after_dec]
    · intro j hj hb
      cases j with
      | zero =>
        change (step rows ⟨pc,bank⟩).2 = true at hb
        simp [hs] at hb
      | succ j =>
        apply hq j (by omega)
        change (step rows ((system rows).advance ⟨pc,bank⟩ (j+1))).2 = true at hb
        have ha : (system rows).advance ⟨pc,bank⟩ (j+1) =
            (system rows).advance (step rows ⟨pc,bank⟩).1 j := by
          have he : j+1 = 1+j := by omega
          rw [he,advance_add]
          rfl
        rw [ha,hs] at hb
        exact hb

def Silent (rows : Array Row) (s t : State) (duration : Nat) : Prop :=
  (system rows).advance s duration = t ∧
    ∀ j, j < duration → ¬ (system rows).BeepFrom s j

theorem silent_trans (rows : Array Row) (a b c : State) (m n : Nat)
    (h₁ : Silent rows a b m) (h₂ : Silent rows b c n) : Silent rows a c (m+n) := by
  constructor
  · rw [advance_add,h₁.1]; exact h₂.1
  · intro j hj hb
    by_cases hlt : j < m
    · exact h₁.2 j hlt hb
    · apply h₂.2 (j-m) (by omega)
      unfold EventSystem.BeepFrom at hb ⊢
      have hsum : j = m+(j-m) := by omega
      rw [hsum,advance_add,h₁.1] at hb
      exact hb

def afterBegin (bank : Nat → Nat) : Nat → Nat :=
  clear 15 (update (.inc 14) (clear 14 (clear 13 bank)))

theorem afterBegin_frame (bank : Nat → Nat) (j : Nat)
    (h13 : j ≠ 13) (h14 : j ≠ 14) (h15 : j ≠ 15) : afterBegin bank j = bank j := by
  simp [afterBegin,clear,update,h13,h14,h15]

theorem afterBegin_values (bank : Nat → Nat) :
    afterBegin bank 13 = 0 ∧ afterBegin bank 14 = 1 ∧ afterBegin bank 15 = 0 := by
  simp [afterBegin,clear,update]

def sourceState (bank : Nat → Nat) (phase : Phase) : SearchState :=
  ⟨bank 11,bank 12,bank 13,bank 14,bank 15,phase⟩

/-- The five source fields refer to the named frame slots in the exact
pre-control grammar. The source-allocation translation is a separate obligation. -/
theorem source_slots_named :
    PreControlGrammar.grammar.names[11]? = some "$liveframe.0.0" ∧
    PreControlGrammar.grammar.names[12]? = some "$liveframe.0.1" ∧
    PreControlGrammar.grammar.names[13]? = some "$liveframe.0.2" ∧
    PreControlGrammar.grammar.names[14]? = some "$liveframe.0.3" ∧
    PreControlGrammar.grammar.names[15]? = some "$liveframe.0.4" := by decide

/-- The graph reset has exactly the controller's candidate-begin data effect,
independently of all other registers. -/
theorem afterBegin_source (bank : Nat → Nat) :
    sourceState (afterBegin bank) .compare = (controllerStep (sourceState bank .begin)).1 := by
  simp [sourceState,afterBegin,clear,update,controllerStep]

/-- The marked graph operation and the subsequent resets implement one
controller `begin` step, with exactly one event and exact full-bank effect. -/
theorem begin_segment (bank : Nat → Nat) :
    let duration := bank 13 + bank 14 + bank 15 + 5
    (system originalRows).advance ⟨1,bank⟩ duration = ⟨6,afterBegin bank⟩ ∧
    (system originalRows).BeepFrom ⟨1,bank⟩ 0 ∧
    (∀ j, 0 < j → j < duration → ¬ (system originalRows).BeepFrom ⟨1,bank⟩ j) ∧
    sourceState (afterBegin bank) .compare = (controllerStep (sourceState bank .begin)).1 := by
  dsimp only
  let b13 := clear 13 bank
  let b14 := clear 14 b13
  let bplus := update (.inc 14) b14
  let b15 := clear 15 bplus
  have hid : update .beep bank = bank := by funext j; rfl
  have hbeep : step originalRows ⟨1,bank⟩ = (⟨2,bank⟩,true) := by
    simp [step,originalRows,observe,hid]
  have hrow2 : originalRows[2]? = some ⟨.dec 13,2,3⟩ := by decide
  have hrow3 : originalRows[3]? = some ⟨.dec 14,3,4⟩ := by decide
  have hrow5 : originalRows[5]? = some ⟨.dec 15,5,6⟩ := by decide
  have h13 : Silent originalRows ⟨2,bank⟩ ⟨3,b13⟩ (bank 13+1) := by
    exact clear_run originalRows 2 3 13 (bank 13) bank hrow2 rfl
  have hv14 : b13 14 = bank 14 := by simp [b13,clear]
  have h14 : Silent originalRows ⟨3,b13⟩ ⟨4,b14⟩ (bank 14+1) := by
    exact clear_run originalRows 3 4 14 (bank 14) b13 hrow3 hv14
  have hincstep : step originalRows ⟨4,b14⟩ = (⟨5,bplus⟩,false) := by
    simp [step,originalRows,observe,bplus]
  have hinc : Silent originalRows ⟨4,b14⟩ ⟨5,bplus⟩ 1 := by
    constructor
    · change (step originalRows ⟨4,b14⟩).1 = _
      simp [hincstep]
    · intro j hj
      have hj0 : j = 0 := by omega
      subst j
      change ¬ (step originalRows ⟨4,b14⟩).2 = true
      simp [hincstep]
  have hv15 : bplus 15 = bank 15 := by simp [bplus,b14,b13,clear,update]
  have h15 : Silent originalRows ⟨5,bplus⟩ ⟨6,b15⟩ (bank 15+1) := by
    exact clear_run originalRows 5 6 15 (bank 15) bplus hrow5 hv15
  have hq := silent_trans originalRows ⟨2,bank⟩ ⟨3,b13⟩ ⟨4,b14⟩ _ _ h13 h14
  have hq := silent_trans originalRows ⟨2,bank⟩ ⟨4,b14⟩ ⟨5,bplus⟩ _ _ hq hinc
  have hq := silent_trans originalRows ⟨2,bank⟩ ⟨5,bplus⟩ ⟨6,b15⟩ _ _ hq h15
  have htime : bank 13 + bank 14 + bank 15 + 5 =
      1 + ((bank 13+1)+(bank 14+1)+1+(bank 15+1)) := by omega
  refine ⟨?_,?_,?_,afterBegin_source bank⟩
  · rw [htime,advance_add]
    change (system originalRows).advance (step originalRows ⟨1,bank⟩).1 _ = _
    rw [hbeep,hq.1]
    rfl
  · change (step originalRows ⟨1,bank⟩).2 = true
    simp [hbeep]
  · intro j hj hjlt hb
    have hqbound : j-1 < (bank 13+1)+(bank 14+1)+1+(bank 15+1) := by omega
    apply hq.2 (j-1) hqbound
    unfold EventSystem.BeepFrom at hb ⊢
    have hj' : j = 1+(j-1) := by omega
    rw [hj',advance_add] at hb
    change (step originalRows ((system originalRows).advance (step originalRows ⟨1,bank⟩).1 (j-1))).2 = true at hb
    rw [hbeep] at hb
    exact hb

/-- A single-event source interval remains a single-event target interval
under any positive, event-exact refinement. -/
theorem unique_event_transfer {S T : Type} {src : EventSystem S} {dst : EventSystem T}
    (r : EventRefinement src dst) (start duration : Nat) (hpos : 0 < duration)
    (hfirst : src.BeepAt start)
    (hquiet : ∀ i, start < i → i < start+duration → ¬ src.BeepAt i) :
    ∃ event, (r.boundary start ≤ event ∧ event < r.boundary (start+duration) ∧ dst.BeepAt event) ∧
      ∀ other, (r.boundary start ≤ other ∧ other < r.boundary (start+duration) ∧ dst.BeepAt other) → other = event := by
  obtain ⟨event,hlo,hhi,hevent⟩ := (r.event_iff start).1 hfirst
  have hlim : r.boundary (start+1) ≤ r.boundary (start+duration) :=
    r.boundary_mono (by omega)
  refine ⟨event,⟨hlo,by omega,hevent⟩,?_⟩
  intro other hother
  obtain ⟨idx,hidxlo,hidxhi,hold,hone⟩ := r.covers_between hother.1 hother.2.1
  have hsrc : src.BeepAt idx := (r.event_iff idx).2 ⟨other,hold,hone,hother.2.2⟩
  have heq : idx = start := by
    by_cases heq : idx = start
    · exact heq
    · exact False.elim (hquiet idx (by omega) hidxhi hsrc)
  subst idx
  exact r.event_unique start other event hold hone hlo hhi hother.2.2 hevent

/-- Whenever the checked graph reaches the candidate-begin boundary, the
pre-control grammar executes a positive finite segment with exactly one event
and reaches the full bank prescribed by the source controller. -/
theorem reachable_begin_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨1,bank⟩) :
    let d := bank 13 + bank 14 + bank 15 + 5
    let r := PreControlGrammar.acceptedRefinement
    r.boundary t < r.boundary (t+d) ∧
    ((ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary (t+d))).bank = afterBegin bank ∧
    sourceState (afterBegin bank) .compare = (controllerStep (sourceState bank .begin)).1 ∧
    ∃ event, (r.boundary t ≤ event ∧ event < r.boundary (t+d) ∧
      (ProducerGrammar.system PreControlGrammar.grammar).BeepAt event) ∧
      ∀ other, (r.boundary t ≤ other ∧ other < r.boundary (t+d) ∧
        (ProducerGrammar.system PreControlGrammar.grammar).BeepAt other) → other = event := by
  dsimp only
  let d := bank 13 + bank 14 + bank 15 + 5
  let r := PreControlGrammar.acceptedRefinement
  have hd : 0 < d := by dsimp [d]; omega
  have hseg := begin_segment bank
  have hend : (system originalRows).run (t+d) = ⟨6,afterBegin bank⟩ := by
    rw [EventSystem.run_add,hstate]
    exact hseg.1
  have hrel := r.related (t+d)
  change ProducerGrammar.Rel originalRows PreControlGrammar.positions _ _ at hrel
  have hbank : ((ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary (t+d))).bank = afterBegin bank := by
    rw [hend] at hrel
    exact hrel.2.1.symm
  have hfirst : (system originalRows).BeepAt t := by
    have hb := hseg.2.1
    change (step originalRows ⟨1,bank⟩).2 = true at hb
    change (step originalRows ((system originalRows).run t)).2 = true
    rw [hstate]
    exact hb
  have hquiet : ∀ i, t < i → i < t+d → ¬ (system originalRows).BeepAt i := by
    intro i hlo hhi hb
    have heq : i = t+(i-t) := by omega
    have hb' : (system originalRows).BeepFrom ⟨1,bank⟩ (i-t) := by
      rw [heq] at hb
      have ht := ((system originalRows).beepAt_add_iff t (i-t)).1 hb
      simpa [hstate] using ht
    exact hseg.2.2.1 (i-t) (by omega) (by dsimp [d] at hhi; omega) hb'
  exact ⟨r.boundary_strict (by omega),hbank,afterBegin_source bank,
    unique_event_transfer r t d hd hfirst hquiet⟩

/-- The graph begins by initializing the source exponent to one. -/
def firstBank : Nat → Nat := update (.inc 12) (fun _ => 0)

theorem first_begin_graph : (system originalRows).run 1 = ⟨1,firstBank⟩ := by
  change (step originalRows ⟨0,fun _ => 0⟩).1 = _
  simp [step,originalRows,observe,firstBank]

/-- From the all-zero graph entry the pre-control grammar reaches the first
abstract comparison with exactly one preceding event. -/
theorem first_comparison_at_grammar :
    let r := PreControlGrammar.acceptedRefinement
    ((ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary 6)).bank = afterBegin firstBank ∧
    sourceState (afterBegin firstBank) .compare = controller.run 1 ∧
    ∃ event, (event < r.boundary 6 ∧ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt event) ∧
      ∀ other, (other < r.boundary 6 ∧ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt other) → other = event := by
  dsimp only
  let r := PreControlGrammar.acceptedRefinement
  have hbegin := reachable_begin_to_grammar 1 firstBank first_begin_graph
  have hz13 : firstBank 13 = 0 := by simp [firstBank,update]
  have hz14 : firstBank 14 = 0 := by simp [firstBank,update]
  have hz15 : firstBank 15 = 0 := by simp [firstBank,update]
  simp only [hz13,hz14,hz15,Nat.zero_add,Nat.add_zero,Nat.reduceAdd] at hbegin
  have hstate : sourceState (afterBegin firstBank) .compare = controller.run 1 := by
    simp [sourceState,afterBegin,firstBank,clear,update,controller,controllerStep,EventSystem.run]
  have hgraphquiet : ¬ (system originalRows).BeepAt 0 := by
    change ¬ (step originalRows ⟨0,fun _ => 0⟩).2 = true
    simp [step,originalRows,observe]
  have hquiet : ∀ u, u < r.boundary 1 → ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u := by
    intro u hu hb
    apply hgraphquiet
    apply (r.event_iff 0).2
    refine ⟨u,?_,by simpa using hu,hb⟩
    simp [r,EventRefinement.boundary_zero]
  obtain ⟨event,hevent,huniq⟩ := hbegin.2.2.2
  refine ⟨hbegin.2.1,hstate,event,⟨hevent.2.1,hevent.2.2⟩,?_⟩
  intro other hother
  by_cases hbefore : other < r.boundary 1
  · exact False.elim (hquiet other hbefore hother.2)
  · apply huniq other
    dsimp only [r] at hbefore hother ⊢
    exact ⟨by omega,hother.1,hother.2⟩

end Shared.PNP.Record285.SourceBegin
