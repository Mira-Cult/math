import Shared.PNP.Record285.PythonControlTypedEndpoint
import Shared.PNP.Record285.PythonControlProgress

/-! The kernel-bound typed listing has the selected machine's event polarity,
and its run never reaches either administrative sink. This does not assert
CPython parsing or execution semantics. -/
namespace Shared.PNP.Record285.PythonControlProgressEndpoint
open Shared.Beeping
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlProgress
open Shared.PNP.Record285.PythonControlTypedEndpoint

theorem typed_progress_endpoint :
    literalSource = renderedSource ∧
    (∀ t, ∃ c, mainSystem.run t = .live c) ∧
    (mainSystem.FiniteEventTimes ↔ ComplexityTheory.P = ComplexityTheory.NP) ∧
    (mainSystem.InfinitelyManyBeeps ↔ ComplexityTheory.P ≠ ComplexityTheory.NP) ∧
    (mainSystem.EventuallySilent ↔ Shared.PNP.Record285.machine.system.EventuallySilent) := by
  exact ⟨typed_endpoint.1,main_runs_live,typed_endpoint.2.1,
    typed_endpoint.2.2.1,typed_endpoint.2.2.2⟩

end Shared.PNP.Record285.PythonControlProgressEndpoint
