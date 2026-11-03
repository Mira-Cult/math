import Shared.PNP.Record285.SourceControllerSimulation
import Shared.PNP.Record285.RelativeEndpoint
import Shared.PNP.Record285.CanonicalPBridge

/-! Consequences of the literal/source event correspondence. The canonical
complexity and paid input-encoding obligations remain explicit. -/
namespace Shared.PNP.Record285.SourceLiteralEndpoint
open Shared.Beeping
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.SourceControllerSimulation
open Shared.PNP.Record285.RelativeEndpoint
open Shared.PNP.Record285.CanonicalPBridge
open Shared.PNP.Record285.CanonicalInput

/-- The literal machine has finitely many marked transitions iff one fixed
positive-exponent source candidate agrees with the bounded reference. -/
theorem literal_finiteEvents_iff_goodCandidate :
    Record285.machine.system.FiniteEventTimes ↔
      ∃ program exponent, 0 < exponent ∧ GoodCandidate program exponent :=
  Record285.machine.system.eventuallySilent_iff_finiteEventTimes.symm.trans
    literal_eventuallySilent_iff_goodCandidate

/-- The same exact literal endpoint in terms of bounded full-relative-tape
runs, still without any canonical complexity assertion. -/
theorem literal_finiteEvents_iff_relativeGood :
    Record285.machine.system.FiniteEventTimes ↔
      ∃ program exponent, 0 < exponent ∧ RelativeGood program exponent := by
  rw [literal_finiteEvents_iff_goodCandidate]
  simp only [goodCandidate_iff_relativeGood]

theorem literal_infinitelyMany_iff_no_relativeGood :
    Record285.machine.system.InfinitelyManyBeeps ↔
      ¬ ∃ program exponent, 0 < exponent ∧ RelativeGood program exponent := by
  rw [literal_infinitelyMany_iff_no_goodCandidate]
  simp only [goodCandidate_iff_relativeGood]

/-- A conditional bridge to canonical P: the paid raw-frame wrapper remains an
explicit unproved premise, and the reference language is not yet shown NP-complete. -/
theorem literal_silent_of_reference_P_and_wrapper
    (hP : ComplexityTheory.IsPolyTime referenceLanguage) (hwrap : FrameEncodingWrapper) :
    Record285.machine.system.EventuallySilent :=
  source_eventuallySilent_iff_literal.1 (source_silent_of_reference_P_and_wrapper hP hwrap)

end Shared.PNP.Record285.SourceLiteralEndpoint
