import Shared.Beeping.NPcoNP.Grammar284NodePairsSource
import Shared.Beeping.NPcoNP.Grammar284Registers
import Shared.Beeping.NPcoNP.Grammar284NodeLeaf

/-! A total parser for one fixed-layout grammar instance: exactly 160 nodes,
12 registers and no input after the final newline. The actual leaf parser is
an explicit parameter; the round trip is conditional on its proved contract.
No theorem here asserts equality with the pinned file. -/
namespace Shared.Beeping.NPcoNP.Grammar284WholeParser
open Shared.Beeping.NPcoNP
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284NodePairs
open Shared.Beeping.NPcoNP.Grammar284NodePairsSource
open Shared.Beeping.NPcoNP.Grammar284OperationLeaf (strip strip_append)

/-- Exact fixed counts and EOF are part of the executable parser. -/
def parse (parseLeaf : Parser) (input : List Char) : Option Grammar := do
  let s ← strip "{\n  \"nodes\": [\n".toList input
  let (ns, s) ← parseNodes parseLeaf 160 s
  let s ← strip "\n  ],\n  \"registers\": [\n".toList s
  let (regs, s) ← Grammar284Registers.parse 12 s
  let s ← strip "  ],\n  \"root\": ".toList s
  let (root, s) ← Grammar284NodeLeaf.parseLine s
  let s ← strip "}\n".toList s
  if s = [] then some ⟨ns.toArray, (regs.map String.ofList).toArray, root⟩ else none

/- Sufficient conditions for renderer recovery; the leaf parser law remains explicit. -/
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem parse_render (parseLeaf : Parser) (good : Leaf → Prop)
    (hleaf : ∀ a tail, good a → parseLeaf (SourceRender.leaf a ++ tail) = some (a,tail))
    (g : Grammar) (hn : g.nodes.size = 160) (hr : g.registers.size = 12)
    (hnodes : ∀ p ∈ g.nodes.toList, good p.1 ∧ good p.2)
    (hregs : ∀ s ∈ g.registers.toList, Grammar284Quoted.safe s.toList = true) :
    parse parseLeaf (SourceRender.render g) = some g := by
  have hn' : g.nodes.toList ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [Array.length_toList, List.length_nil, hn] at hlen
    contradiction
  have hr' : g.registers.toList ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [Array.length_toList, List.length_nil, hr] at hlen
    contradiction
  have hns := parseNodes_render parseLeaf SourceRender.leaf good hleaf
    g.nodes.toList hnodes ('\n' :: SourceRender.footer g)
  have hns' : parseNodes parseLeaf 160 (SourceRender.nodes g.nodes.toList (SourceRender.footer g)) =
      some (g.nodes.toList, '\n' :: SourceRender.footer g) := by
    rw [renderNodes_eq_nodes_nonempty _ _ hn']
    simpa [hn] using hns
  have hregsafe : ∀ chars ∈ g.registers.toList.map String.toList,
      Grammar284Quoted.safe chars = true := by
    intro chars hc
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
    exact hregs s hs
  let rest : List Char := "  ],\n  \"root\": ".toList ++
    Nat.toDigits 10 g.root ++ '\n' :: "}\n".toList
  have hrs := Grammar284Registers.parse_render
    (g.registers.toList.map String.toList) rest hregsafe
  rw [Grammar284Registers.render_eq_source g.registers.toList hr'] at hrs
  have hrs' : Grammar284Registers.parse 12
      (SourceRender.join (g.registers.toList.map SourceRender.register) ++ '\n' :: rest) =
      some (g.registers.toList.map String.toList, rest) := by
    simpa [hr, List.append_assoc] using hrs
  unfold parse SourceRender.render
  rw [strip_append]
  simp only [bind, Option.bind]
  rw [hns']
  simp only [bind, Option.bind]
  unfold SourceRender.footer
  rw [show ('\n' :: ("  ],\n  \"registers\": [\n".toList ++
      SourceRender.join (g.registers.toList.map SourceRender.register) ++
      "\n  ],\n  \"root\": ".toList ++ (toString g.root).toList ++ "\n}\n".toList)) =
      ("\n  ],\n  \"registers\": [\n".toList ++
      (SourceRender.join (g.registers.toList.map SourceRender.register) ++ '\n' :: rest)) by
        simp [rest, Nat.toString_eq_repr, Nat.toList_repr, List.append_assoc]]
  rw [strip_append]
  simp only [bind, Option.bind]
  rw [hrs']
  simp only [bind, Option.bind]
  have hstrip : strip "  ],\n  \"root\": ".toList rest =
      some (Nat.toDigits 10 g.root ++ '\n' :: "}\n".toList) := by
    dsimp only [rest]
    exact strip_append _ _
  rw [hstrip]
  simp only [bind, Option.bind]
  rw [Grammar284NodeLeaf.parseLine_repr]
  simp only [bind, Option.bind]
  rw [show strip "}\n".toList "}\n".toList = some [] by rfl]
  simp [String.ofList_toList]

end Shared.Beeping.NPcoNP.Grammar284WholeParser
