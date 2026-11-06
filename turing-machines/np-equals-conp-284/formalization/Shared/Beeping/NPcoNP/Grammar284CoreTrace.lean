import Shared.Beeping.NPcoNP.Grammar284CoreBinding

/-! Finite graph execution from the restricted parse of the embedded grammar.
This does not establish Python compiler correspondence, physical-tape
refinement, or any complexity-class equivalence. -/
namespace Shared.Beeping.NPcoNP.Grammar284CoreTrace
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.GraphCandidate284
open Shared.Beeping.NPcoNP.GraphExtendedTrace
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Grammar284CoreBinding

/-- The parsed and interpreted source graph executes any finite register trace
without decoder failure, producing the target configuration and ordered word. -/
theorem embeddedGraph_run (c : Cfg) (n : Nat) :
    ((Grammar284ParseSource.parse Grammar284.SourceChars.source.toList).bind
      (fun g => coreGraph g 53)).bind (fun g => graphTrace g c n) =
    some (target.system.advance c n, target.system.wordFrom c n) :=
  bind_of _ _ graph _ embeddedCoreGraph (Grammar284CoreAST.graph_run c n)

end Shared.Beeping.NPcoNP.Grammar284CoreTrace
