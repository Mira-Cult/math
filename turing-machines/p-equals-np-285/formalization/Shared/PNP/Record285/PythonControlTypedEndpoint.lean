import Shared.PNP.Record285.PythonControlSimulation
import Shared.PNP.Record285.PythonSyntaxCertificate
import Shared.PNP.Record285.LiteralEndpoint

/-! The typed listing is kernel-bound to the frozen source text and its
interpreter has the same finite/infinite event polarity as the literal
285-state machine. CPython parsing and execution are not asserted. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlTypedEndpoint
open Shared.Beeping
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSimulation
open Shared.PNP.Record285.PythonSyntax

theorem typed_silent_iff_literal :
    mainSystem.EventuallySilent ↔ Shared.PNP.Record285.machine.system.EventuallySilent :=
  eventuallySilent_iff.symm.trans
    (Shared.PNP.Record285.AlignedPhysical.refinement.eventuallySilent_iff.trans
      Shared.PNP.Record285.DirectEndpoint.post_silent_iff_blank_start)

theorem typed_silent_iff_P_eq_NP :
    mainSystem.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP :=
  typed_silent_iff_literal.trans Shared.PNP.Record285.DirectEndpoint.literal_silent_iff_P_eq_NP

theorem typed_endpoint :
    literalSource = renderedSource ∧
    (mainSystem.FiniteEventTimes ↔ ComplexityTheory.P = ComplexityTheory.NP) ∧
    (mainSystem.InfinitelyManyBeeps ↔ ComplexityTheory.P ≠ ComplexityTheory.NP) ∧
    (mainSystem.EventuallySilent ↔ Shared.PNP.Record285.machine.system.EventuallySilent) := by
  refine ⟨literal_source_is_rendered,?_,?_,typed_silent_iff_literal⟩
  · exact mainSystem.eventuallySilent_iff_finiteEventTimes.symm.trans typed_silent_iff_P_eq_NP
  · rw [← EventSystem.not_eventuallySilent_iff_infinitelyMany]
    exact not_congr typed_silent_iff_P_eq_NP

end Shared.PNP.Record285.PythonControlTypedEndpoint
