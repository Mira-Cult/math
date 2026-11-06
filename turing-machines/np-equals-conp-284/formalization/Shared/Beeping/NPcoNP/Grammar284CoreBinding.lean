import Shared.Beeping.NPcoNP.Grammar284CoreAST
import Shared.Beeping.NPcoNP.Grammar284ParseSource

/-! The restricted parser and Lean graph extraction compose for the embedded
producer source. This does not establish a file hash, correspondence with the
producer's Python algorithm, or a binary-tape refinement. -/
namespace Shared.Beeping.NPcoNP.Grammar284CoreBinding
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.GraphCandidate284

/-- Compose two successful optional computations without recomputing their data. -/
theorem bind_of {α β : Type} (x : Option α) (f : α → Option β) (a : α) (b : β)
    (ha : x = some a) (hb : f a = some b) : x.bind f = some b := by
  cases ha
  exact hb

/-- Parsing the embedded source with the restricted parser, then interpreting
its grammar, returns the checked 185-row candidate graph. -/
theorem embeddedCoreGraph :
    (Grammar284ParseSource.parse Grammar284.SourceChars.source.toList).bind
      (fun g => coreGraph g 53) = some graph :=
  bind_of (Grammar284ParseSource.parse Grammar284.SourceChars.source.toList)
    (fun g => coreGraph g 53) producerGrammar graph
    Grammar284ParseSource.parse_embedded_source Grammar284CoreAST.producerCoreGraph

end Shared.Beeping.NPcoNP.Grammar284CoreBinding
