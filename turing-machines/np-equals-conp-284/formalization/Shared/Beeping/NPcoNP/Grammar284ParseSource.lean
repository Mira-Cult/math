import Shared.Beeping.NPcoNP.Grammar284WholeParser
import Shared.Beeping.NPcoNP.Grammar284LeafParser
import Shared.Beeping.NPcoNP.Grammar284DataChecks
import Shared.Beeping.NPcoNP.Grammar284SourceComposition

/-! Kernel-checked fixed-layout parsing of the embedded producer grammar.
This covers the selected bytes, counts, and final newline/EOF. It is not a
claim about arbitrary JSON or the later on-disk state of the source file. -/
namespace Shared.Beeping.NPcoNP.Grammar284ParseSource
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Quoted
open Shared.Beeping.NPcoNP.Grammar284LeafParser

def parse : List Char → Option Grammar := Grammar284WholeParser.parse Grammar284LeafParser.parse

theorem good_of_safeLeaf (a : Leaf) (h : safeLeaf a = true) : good a := by
  cases a <;> simp_all [safeLeaf, good]

theorem producer_nodes_good :
    ∀ p ∈ producerGrammar.nodes.toList, good p.1 ∧ good p.2 := by
  intro p hp
  have h := List.all_eq_true.mp producer_operations_safe p hp
  simp only [Bool.and_eq_true] at h
  exact ⟨good_of_safeLeaf p.1 h.1, good_of_safeLeaf p.2 h.2⟩

theorem producer_registers_good :
    ∀ s ∈ producerGrammar.registers.toList, safe s.toList = true := by
  exact List.all_eq_true.mp producer_registers_safe

theorem parse_rendered_producer :
    parse (SourceRender.render producerGrammar) = some producerGrammar := by
  unfold parse
  apply Grammar284WholeParser.parse_render Grammar284LeafParser.parse good
  · intro a tail ha
    rw [← render_eq_source_leaf]
    exact Grammar284LeafParser.parse_render a tail ha
  · exact producerGrammar_node_count
  · exact producerGrammar_register_count
  · exact producer_nodes_good
  · exact producer_registers_good

/-- The total fixed-count parser, including its explicit EOF check, recovers
exactly the selected semantic grammar from all embedded source characters. -/
theorem parse_embedded_source :
    parse SourceChars.source.toList = some producerGrammar := by
  rw [SourceComposition.source_to_render]
  exact parse_rendered_producer

end Shared.Beeping.NPcoNP.Grammar284ParseSource
