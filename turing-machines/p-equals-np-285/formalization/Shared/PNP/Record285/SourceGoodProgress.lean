import Shared.PNP.Record285.PayloadClosed

/-! Make explicit the continued correct comparisons behind eventual silence.
This is a source/graph progress theorem; it does not claim a new direct
whole-tape source refinement. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.SourceGoodProgress
open Shared.Beeping
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.SourceControllerSimulation

/-- A good candidate somewhere in the enumeration implies that the first
good candidate is reached, and thereafter every source step checks the next
input with the same program and exponent. -/
theorem good_candidate_progress
    (hexists : ∃ program exponent, 0 < exponent ∧ GoodCandidate program exponent) :
    ∃ start program exponent, 0 < exponent ∧ GoodCandidate program exponent ∧
      ∀ j, let s := controller.run (start+j)
        s.program = program ∧ s.exponent = exponent ∧ s.phase = .compare ∧
        InputInvariant s ∧ inputOrdinal s.n s.remaining = j ∧
        mismatch s.program s.exponent s.n s.radix s.remaining = false := by
  classical
  obtain ⟨p,e,he,hgood⟩ := hexists
  let rank := triangle (p+e-1)+(e-1)
  have hrank : candidateAt rank = (p,e) := candidateAfter_covers p e he
  have hsome : ∃ i, GoodCandidate (candidateAt i).1 (candidateAt i).2 := by
    exact ⟨rank,by simpa [hrank] using hgood⟩
  let i := Nat.find hsome
  have hi : GoodCandidate (candidateAt i).1 (candidateAt i).2 := Nat.find_spec hsome
  have hbad : ∀ j, j < i → ¬ GoodCandidate (candidateAt j).1 (candidateAt j).2 := by
    intro j hj
    exact Nat.find_min hsome hj
  obtain ⟨t,_,hat⟩ := reachCandidate i hbad
  rcases hat with ⟨hphase,hp,he'⟩
  let program := (candidateAt i).1
  let exponent := (candidateAt i).2
  have hg : GoodCandidate (controller.run t).program (controller.run t).exponent := by
    simpa [hp,he'] using hi
  refine ⟨t+1,program,exponent,candidateAt_positive i,hi,?_⟩
  intro j
  have hr := controller_from_begin t (controller.run t) rfl hphase j
  have hs := scan_progress (controller.run t).program (controller.run t).exponent hg j
  dsimp only at hs ⊢
  rw [show t+1+j = (t+1)+j by rfl] at hr
  rw [hr]
  rcases hs with ⟨hprog,hexp,hcompare,hinv,hord⟩
  refine ⟨by simpa [program,hp] using hprog,by simpa [exponent,he'] using hexp,
    hcompare,hinv,hord,?_⟩
  rw [hprog,hexp,hinv.1]
  exact hg _ _ (by simpa [← hinv.1] using hinv.2)

/-- The literal machine's eventual silence implies continued correct source
comparisons at every later source step, with unbounded input index. -/
theorem finite_literal_events_imply_continued_comparisons
    (hfinite : Shared.PNP.Record285.machine.system.FiniteEventTimes) :
    ∃ start program exponent, 0 < exponent ∧ GoodCandidate program exponent ∧
      ∀ j, let s := controller.run (start+j)
        s.program = program ∧ s.exponent = exponent ∧ s.phase = .compare ∧
        InputInvariant s ∧ inputOrdinal s.n s.remaining = j ∧
        mismatch s.program s.exponent s.n s.radix s.remaining = false := by
  exact good_candidate_progress
    (Shared.PNP.Record285.SourceLiteralEndpoint.literal_finiteEvents_iff_goodCandidate.1 hfinite)

/-- Under P = NP the same explicitly identified source computation continues
through every input index. -/
theorem P_eq_NP_implies_continued_comparisons (hP : ComplexityTheory.P = ComplexityTheory.NP) :
    ∃ start program exponent, 0 < exponent ∧ GoodCandidate program exponent ∧
      ∀ j, let s := controller.run (start+j)
        s.program = program ∧ s.exponent = exponent ∧ s.phase = .compare ∧
        InputInvariant s ∧ inputOrdinal s.n s.remaining = j ∧
        mismatch s.program s.exponent s.n s.radix s.remaining = false := by
  exact finite_literal_events_imply_continued_comparisons
    (Shared.PNP.Record285.PayloadClosed.literal_finiteEvents_iff_P_eq_NP.2 hP)

/-- These comparisons also have strictly advancing graph boundaries. Each
complete graph segment is silent, and its boundary retains the established
source-to-graph state relation. This does not assert a direct physical-tape
relation through the separate compiler passes. -/
theorem finite_literal_events_have_cofinal_graph_comparisons
    (hfinite : Shared.PNP.Record285.machine.system.FiniteEventTimes) :
    ∃ start program exponent, 0 < exponent ∧ GoodCandidate program exponent ∧
      ∀ j,
        let i := start+j
        let r := simulation.toEventRefinement
        let b := r.boundary i
        let s := controller.run i
        let g := shiftedGraph.run b
        j ≤ b ∧ b < r.boundary (i+1) ∧ SourceControllerSimulation.Rel s g ∧ g.index = 6 ∧
        inputOrdinal s.n s.remaining = j ∧
        mismatch s.program s.exponent s.n s.radix s.remaining = false ∧
        ∀ k, b ≤ k → k < r.boundary (i+1) → ¬ shiftedGraph.BeepAt k := by
  obtain ⟨start,program,exponent,hpos,hgood,hprogress⟩ :=
    finite_literal_events_imply_continued_comparisons hfinite
  refine ⟨start,program,exponent,hpos,hgood,?_⟩
  intro j
  let i := start+j
  let r := simulation.toEventRefinement
  have hs := hprogress j
  change (controller.run i).program = program ∧ (controller.run i).exponent = exponent ∧
      (controller.run i).phase = .compare ∧ InputInvariant (controller.run i) ∧
      inputOrdinal (controller.run i).n (controller.run i).remaining = j ∧
      mismatch (controller.run i).program (controller.run i).exponent
        (controller.run i).n (controller.run i).radix (controller.run i).remaining = false at hs
  have hrel := r.related i
  have hindex : (shiftedGraph.run (r.boundary i)).index = 6 := by
    simpa [SourceControllerSimulation.Rel,hs.2.2.1] using hrel.2.2
  have hnot : ¬ controller.BeepAt i := by
    intro hb
    have hp := (controllerStep_beep (controller.run i)).1 hb
    rw [hs.2.2.1] at hp
    cases hp
  refine ⟨?_,r.progress i,hrel,hindex,hs.2.2.2.2.1,hs.2.2.2.2.2,?_⟩
  · change j ≤ r.boundary (start+j)
    have hb := r.boundary_ge (start+j)
    omega
  · intro k hlo hhi he
    exact hnot ((r.event_iff i).2 ⟨k,hlo,hhi,he⟩)

end Shared.PNP.Record285.SourceGoodProgress
