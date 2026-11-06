import Shared.Beeping.NPcoNP.Source284GraphTableConditional
import Shared.Beeping.NPcoNP.Source284AllInputReferenceCoverage

/-! The canonical NP=coNP characterization for the coalesced register graph
is now unconditional. For the selected physical table the only remaining
argument in this endpoint is the explicit progress-sensitive, event-word
simulation from that graph, including paid startup and full target coverage.
This module does not construct that simulation. -/
namespace Shared.Beeping.NPcoNP.Source284TableSimulationEndpoint

open ComplexityTheory
open Shared.Beeping.NPcoNP.Source284GraphTableConditional
open Shared.Beeping.NPcoNP.Source284AllInputReferenceCoverage

/-- The literal selected table has the requested canonical equivalence once
its concrete progress-sensitive graph-to-table certificate is constructed. -/
theorem selected_table_silent_iff_classes
    (binding : GraphTableSimulation Table284.machine) :
    Table284.machine.system.EventuallySilent ↔ NP = coNP :=
  (eventuallySilent_iff_graph Table284.machine binding).trans
    graph_eventuallySilent_iff_classes

end Shared.Beeping.NPcoNP.Source284TableSimulationEndpoint

#print axioms Shared.Beeping.NPcoNP.Source284TableSimulationEndpoint.selected_table_silent_iff_classes
