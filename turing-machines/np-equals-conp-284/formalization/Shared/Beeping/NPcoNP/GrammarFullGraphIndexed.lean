import Shared.Beeping.NPcoNP.GrammarFullGraphCert

/-! An indexed version of the ordered row certificate. It enables independent
finite index shards; the expansion and all row equations remain premises. -/

namespace Shared.Beeping.NPcoNP.Grammar284

theorem fullGraph_of_indexed_rows (g : Grammar) (fuel : Nat)
    (e : Expansion) (rows : Array Row)
    (he : expand g.nodes fuel (.node g.root) [true,true,false] [] {} = some e)
    (hsize : e.leaves.size = rows.size)
    (hr : ∀ (i : Fin e.leaves.size),
      fullRow e.starts e.leaves[i] =
        some (rows[i.val]'(by simpa [← hsize] using i.isLt))) :
    fullGraph g fuel = some rows := by
  have hf : fullGraph g fuel = some rows.toList.toArray := by
    apply fullGraph_of_expansion_rows g fuel e rows.toList he
    apply List.forall₂_iff_get.mpr
    constructor
    · simpa using hsize
    · intro i hi1 hi2
      have hi : i < e.leaves.size := by simpa using hi1
      simpa using hr ⟨i, hi⟩
  simpa using hf

end Shared.Beeping.NPcoNP.Grammar284
