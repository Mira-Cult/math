import Shared.Beeping.NPcoNP.Source284GraphCanonical
import Shared.Beeping.NPcoNP.Table284LiteralBinding
import Shared.Beeping.WordEventCoverageBoot

/-! Explicit machine-binding endpoint. A caller must supply a genuine
progress-sensitive ordered-word simulation from the proved register graph to
the named binary machine, including its paid finite startup. Candidate coverage
is separately required for the reverse class implication. -/
namespace Shared.Beeping.NPcoNP.Source284GraphTableConditional
open ComplexityTheory PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284CanonicalConditional

/-- No startup is free: the supplied certificate includes its length, silent
word and initial relation, followed by positive, finite event-preserving
segments covering the complete target run. -/
abbrev GraphTableSimulation {n : Nat} (M : Machine n) :=
  PASoundness.SegmentSimulation target.system (machineWordSystem M (BitLabels.fromFlags M))

theorem eventuallySilent_iff_graph {n : Nat} (M : Machine n)
    (binding : GraphTableSimulation M) :
    M.system.EventuallySilent ↔ target.system.erase.EventuallySilent := by
  have h := WordEventCoverageBoot.eventuallySilent_iff binding
  rw [fromFlags_erase] at h
  exact h.symm

/-- Any actual finite-table simulation certificate transfers the unconditional
one-way canonical class consequence to that machine. -/
theorem eventuallySilent_implies_classes {n : Nat} (M : Machine n)
    (binding : GraphTableSimulation M) :
    M.system.EventuallySilent → NP = coNP := by
  intro h
  exact Source284GraphCanonical.eventuallySilent_implies_classes
    ((eventuallySilent_iff_graph M binding).mp h)

/-- The two remaining obligations for a full machine-level endpoint are
explicit: the machine simulation and fixed-candidate source coverage. -/
theorem eventuallySilent_iff_classes {n : Nat} (M : Machine n)
    (binding : GraphTableSimulation M)
    (coverage : referenceLanguageᶜ ∈ NP →
      ∃ j, candidateLanguage j = referenceLanguageᶜ) :
    M.system.EventuallySilent ↔ NP = coNP :=
  (eventuallySilent_iff_graph M binding).trans
    (Source284GraphCanonical.eventuallySilent_iff_classes coverage)

/-- The selected serialized 284-state machine is named here, but the
simulation certificate is still an unproved explicit argument. -/
theorem selected_table_silent_implies_classes
    (binding : GraphTableSimulation Table284.machine) :
    Table284.machine.system.EventuallySilent → NP = coNP :=
  eventuallySilent_implies_classes Table284.machine binding

theorem selected_table_silent_iff_classes
    (binding : GraphTableSimulation Table284.machine)
    (coverage : referenceLanguageᶜ ∈ NP →
      ∃ j, candidateLanguage j = referenceLanguageᶜ) :
    Table284.machine.system.EventuallySilent ↔ NP = coNP :=
  eventuallySilent_iff_classes Table284.machine binding coverage

/-- For the selected literal table, the unresolved operational inputs are a
physical graph simulation and the explicit guarded finite-row compiler. -/
theorem selected_table_silent_iff_classes_of_guardCompiler
    (binding : GraphTableSimulation Table284.machine)
    (compiler : Source284GuardCompilerInterface.GuardCompiler) :
    Table284.machine.system.EventuallySilent ↔ NP = coNP :=
  (eventuallySilent_iff_graph Table284.machine binding).trans
    (Source284GraphCanonical.eventuallySilent_iff_classes_of_guardCompiler compiler)

end Shared.Beeping.NPcoNP.Source284GraphTableConditional
