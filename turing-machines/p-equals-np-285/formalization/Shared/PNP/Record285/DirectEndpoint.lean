import Shared.PNP.Record285.AlignedPhysicalInitialization
import Shared.PNP.Record285.PayloadClosed

/-! The literal complexity endpoint derived through the direct full-tape,
positive-progress source refinement. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.DirectEndpoint
open Shared.Beeping
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.CanonicalInput
open Shared.PNP.Record285.AlignedPhysical

/-- The finite literal initialization prefix does not affect eventual
silence. In fact it is proved event-free by `initial_prefix_silent`. -/
theorem post_silent_iff_blank_start :
    postInitialization.EventuallySilent ↔ Shared.PNP.Record285.machine.system.EventuallySilent := by
  rw [Shared.PNP.Record285.machine.system.eventuallySilent_iff_shift (boundary 0)]
  constructor
  · rintro ⟨T,hT⟩
    refine ⟨T,?_⟩
    intro t ht he
    exact hT t ht ((post_beep t).2 he)
  · rintro ⟨T,hT⟩
    refine ⟨T,?_⟩
    intro t ht he
    exact hT t ht ((post_beep t).1 he)

/-- A successful source candidate and the proved candidate simulator give
canonical P membership of the complete all-bitstring reference language. -/
theorem source_silent_iff_reference_P :
    controller.EventuallySilent ↔ ComplexityTheory.IsPolyTime referenceLanguage := by
  constructor
  · intro hs
    obtain ⟨program,exponent,_,hgood⟩ := eventuallySilent_iff_goodCandidate.1 hs
    exact Shared.PNP.Record285.CandidateCanonicalParsing.reference_isPolyTime_of_good program exponent hgood
  · exact Shared.PNP.Record285.PayloadClosed.source_silent_of_reference_P

/-- The selected literal machine is silent exactly when canonical P = NP,
using the direct, complete-tape, event-exact source refinement. -/
theorem literal_silent_iff_P_eq_NP :
    Shared.PNP.Record285.machine.system.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP := by
  calc
    _ ↔ postInitialization.EventuallySilent := post_silent_iff_blank_start.symm
    _ ↔ controller.EventuallySilent := refinement.eventuallySilent_iff.symm
    _ ↔ ComplexityTheory.IsPolyTime referenceLanguage := source_silent_iff_reference_P
    _ ↔ ComplexityTheory.P = ComplexityTheory.NP := Shared.PNP.Record285.ReferenceVerifier.reference_P_iff_P_eq_NP

theorem literal_finiteEvents_iff_P_eq_NP :
    Shared.PNP.Record285.machine.system.FiniteEventTimes ↔ ComplexityTheory.P = ComplexityTheory.NP :=
  Shared.PNP.Record285.machine.system.eventuallySilent_iff_finiteEventTimes.symm.trans
    literal_silent_iff_P_eq_NP

theorem literal_infinitelyMany_iff_P_ne_NP :
    Shared.PNP.Record285.machine.system.InfinitelyManyBeeps ↔ ComplexityTheory.P ≠ ComplexityTheory.NP := by
  rw [← EventSystem.not_eventuallySilent_iff_infinitelyMany]
  exact not_congr literal_silent_iff_P_eq_NP

end Shared.PNP.Record285.DirectEndpoint
