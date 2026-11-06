import Shared.Beeping.NPcoNP.GrammarFullRowsCoverage
import Shared.Beeping.NPcoNP.Grammar284ContractCoverage
import Shared.Beeping.NPcoNP.GraphCandidate284Coverage
import Shared.Beeping.NPcoNP.GraphExtendedTrace

/-! Checked Lean AST-to-graph and finite graph execution. The restricted source
parser, source file identity, Python algorithm and physical tape refinement
are separate obligations. -/
namespace Shared.Beeping.NPcoNP.Grammar284CoreAST
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.GrammarFullRowsCoverage
open Shared.Beeping.NPcoNP.Grammar284ContractCoverage
open Shared.Beeping.NPcoNP.GraphCandidate284
open Shared.Beeping.NPcoNP.GraphCandidate284Coverage
open Shared.Beeping.NPcoNP.GraphExtendedTrace
open Shared.Beeping.NPcoNP.Parent290Coalesced

theorem producerCoreGraph : coreGraph producerGrammar 53 = some graph := by
  simp [coreGraph, producerFullGraph, producerContract]

theorem graph_run (c : Cfg) (n : Nat) :
    graphTrace graph c n = some (target.system.advance c n, target.system.wordFrom c n) :=
  graphTrace_eq graph target graph_matches c n

end Shared.Beeping.NPcoNP.Grammar284CoreAST
