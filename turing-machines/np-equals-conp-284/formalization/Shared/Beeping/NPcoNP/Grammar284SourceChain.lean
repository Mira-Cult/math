import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! Ordered composition of local source-rendering equations. This does not
assert any equation about the pinned grammar or source bytes. -/

namespace Shared.Beeping.NPcoNP.Grammar284.SourceRender

/-- A chain specifies the exact current and remaining character lists for
each successive node. The final node has a newline; earlier nodes have a
comma and newline. -/
inductive RenderChain : List (Leaf × Leaf) → List Char → List Char → Prop
  | nil (tail : List Char) : RenderChain [] tail tail
  | last (p : Leaf × Leaf) (current tail : List Char) :
      current = node p ++ "\n".toList ++ tail →
      RenderChain [p] current tail
  | cons (p q : Leaf × Leaf) (rest : List (Leaf × Leaf))
      (current middle tail : List Char) :
      current = node p ++ ",\n".toList ++ middle →
      RenderChain (q :: rest) middle tail →
      RenderChain (p :: q :: rest) current tail

/-- Local equations in a complete ordered chain determine the rendered node
list, without evaluating or skipping an unspecified suffix. -/
theorem nodes_eq_of_chain {xs : List (Leaf × Leaf)} {current tail : List Char}
    (h : RenderChain xs current tail) : nodes xs tail = current := by
  induction h with
  | nil => rfl
  | last p current tail heq =>
      simpa only [nodes] using heq.symm
  | cons p q rest current middle tail heq hchain ih =>
      simp only [nodes]
      rw [ih]
      exact heq.symm

end Shared.Beeping.NPcoNP.Grammar284.SourceRender
