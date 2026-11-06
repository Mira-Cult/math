import Shared.Beeping.NPcoNP.GrammarGraph284

/-! A compositional certificate interface for the row-resolution stage of the
finite grammar interpreter. It does not assert a specific expansion, resolved
row list, contracted graph, or correspondence to external source bytes. -/

namespace Shared.Beeping.NPcoNP.Grammar284

/-- Independently checked per-leaf row results determine the complete ordered
`mapM` result. In particular, missing, extra, and reordered rows cannot pass. -/
theorem rows_mapM_of_forall₂ (starts : Array (Path × Nat))
    {leaves : List (Path × String)} {rows : List Row}
    (h : List.Forall₂ (fun leaf row => fullRow starts leaf = some row) leaves rows) :
    leaves.mapM (fullRow starts) = some rows := by
  induction h with
  | nil => rfl
  | cons h hs ih => simp [h, ih]

/-- The finite expansion result and ordered row certificate determine the
full graph. Both are explicit premises; no producer computation is assumed. -/
theorem fullGraph_of_expansion_rows (g : Grammar) (fuel : Nat)
    (e : Expansion) (rows : List Row)
    (he : expand g.nodes fuel (.node g.root) [true,true,false] [] {} = some e)
    (hr : List.Forall₂ (fun leaf row => fullRow e.starts leaf = some row)
      e.leaves.toList rows) :
    fullGraph g fuel = some rows.toArray := by
  have hm := rows_mapM_of_forall₂ e.starts hr
  simp [fullGraph, he, hm]

end Shared.Beeping.NPcoNP.Grammar284
