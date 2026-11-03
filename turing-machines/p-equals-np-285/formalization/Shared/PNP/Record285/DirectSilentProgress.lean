import Shared.PNP.Record285.DirectEndpoint
import Shared.PNP.Record285.SourceGoodProgress

/-! In the silent case, every sufficiently late literal transition belongs
to a finite segment implementing a correct source comparison. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.DirectSilentProgress
open Shared.Beeping
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.AlignedPhysical

theorem boundary_mono {i j : Nat} (h : i ≤ j) : boundary i ≤ boundary j := by
  by_cases he : i = j
  · rw [he]
  · exact Nat.le_of_lt (boundary_strict (by omega : i < j))

/-- If P = NP, one fixed good candidate is eventually checked on every input
in order. Every subsequent literal transition belongs to the corresponding
positive, full-tape-refined comparison segment and is unmarked. -/
theorem P_eq_NP_silence_is_continued_correct_work (hP : ComplexityTheory.P = ComplexityTheory.NP) :
    ∃ start program exponent, 0 < exponent ∧ GoodCandidate program exponent ∧
      ∀ t, boundary start ≤ t →
        ∃ j, let i := start+j
          boundary i ≤ t ∧ t < boundary (i+1) ∧
          Rel (controller.run i) (Shared.PNP.Record285.machine.system.run (boundary i)) ∧
          (controller.run i).program = program ∧ (controller.run i).exponent = exponent ∧
          (controller.run i).phase = .compare ∧ InputInvariant (controller.run i) ∧
          inputOrdinal (controller.run i).n (controller.run i).remaining = j ∧
          mismatch (controller.run i).program (controller.run i).exponent
            (controller.run i).n (controller.run i).radix (controller.run i).remaining = false ∧
          ¬ Shared.PNP.Record285.machine.system.BeepAt t := by
  have href : ComplexityTheory.IsPolyTime CanonicalInput.referenceLanguage :=
    Shared.PNP.Record285.ReferenceVerifier.reference_P_iff_P_eq_NP.2 hP
  have hsource : controller.EventuallySilent :=
    Shared.PNP.Record285.DirectEndpoint.source_silent_iff_reference_P.2 href
  obtain ⟨start,program,exponent,hpos,hgood,hprogress⟩ :=
    Shared.PNP.Record285.SourceGoodProgress.good_candidate_progress
      (eventuallySilent_iff_goodCandidate.1 hsource)
  refine ⟨start,program,exponent,hpos,hgood,?_⟩
  intro t ht
  have h0 : boundary 0 ≤ t := le_trans (initial_le_boundary start) ht
  let r := refinement
  obtain ⟨i,hlo,hhi⟩ := r.covers (t-boundary 0)
  have heq : boundary 0+(t-boundary 0)=t := by omega
  have hlo' : boundary i ≤ t := by
    have hh := relativeBoundary_offset i
    change relativeBoundary i ≤ t-boundary 0 at hlo
    omega
  have hhi' : t < boundary (i+1) := by
    have hh := relativeBoundary_offset (i+1)
    change t-boundary 0 < relativeBoundary (i+1) at hhi
    omega
  have hi : start ≤ i := by
    by_cases h : start ≤ i
    · exact h
    · have hm := boundary_mono (show i+1 ≤ start by omega)
      omega
  let j := i-start
  have hij : start+j = i := by dsimp [j]; omega
  have hp := hprogress j
  rw [hij] at hp
  have hnot : ¬ controller.BeepAt i := by
    intro he
    have hh := (controllerStep_beep (controller.run i)).1 he
    rw [hp.2.2.1] at hh
    cases hh
  refine ⟨j,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [hij] using hlo'
  · simpa [hij] using hhi'
  · simpa [hij] using related_at_boundary i
  · simpa [hij] using hp.1
  · simpa [hij] using hp.2.1
  · simpa [hij] using hp.2.2.1
  · simpa [hij] using hp.2.2.2.1
  · simpa [hij] using hp.2.2.2.2.1
  · simpa [hij] using hp.2.2.2.2.2
  · intro he
    exact hnot ((boundary_event_iff i).2 ⟨t,hlo',hhi',he⟩)

end Shared.PNP.Record285.DirectSilentProgress
