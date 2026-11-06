import Shared.Beeping.NPcoNP.GrammarFullGraphIndexed

/-! Executable per-index checks for an arbitrary expansion and candidate full
row array. A passing check is only a certificate for the supplied data; no
producer expansion or physical table identity is asserted here. -/
namespace Shared.Beeping.NPcoNP.Grammar284

/-- Check one row. Missing leaves or candidate rows are rejected. -/
def indexedRowCheck (e : Expansion) (rows : Array Row) (i : Nat) : Bool :=
  match e.leaves[i]?, rows[i]? with
  | some leaf, some row => fullRow e.starts leaf == some row
  | _, _ => false

/-- A bounded, consecutive shard of per-index checks. -/
def indexedRowShard (e : Expansion) (rows : Array Row) (lo len : Nat) : Bool :=
  (List.range len).all fun k => indexedRowCheck e rows (lo + k)

theorem indexedRowCheck_sound (e : Expansion) (rows : Array Row) (i : Nat)
    (hleaf : i < e.leaves.size) (hrow : i < rows.size)
    (h : indexedRowCheck e rows i = true) :
    fullRow e.starts e.leaves[i] = some rows[i] := by
  simpa [indexedRowCheck, hleaf, hrow] using h

theorem indexedRowShard_sound (e : Expansion) (rows : Array Row) (lo len i : Nat)
    (h : indexedRowShard e rows lo len = true)
    (hlo : lo ≤ i) (hhi : i < lo + len) : indexedRowCheck e rows i = true := by
  have h' := List.all_eq_true.mp h
  have hm : i - lo ∈ List.range len := by simp; omega
  have hh := h' (i-lo) hm
  simpa [Nat.add_sub_of_le hlo] using hh

theorem fullGraph_of_checked_rows (g : Grammar) (fuel : Nat)
    (e : Expansion) (rows : Array Row)
    (he : expand g.nodes fuel (.node g.root) [true,true,false] [] {} = some e)
    (hsize : e.leaves.size = rows.size)
    (hchecks : ∀ i < e.leaves.size, indexedRowCheck e rows i = true) :
    fullGraph g fuel = some rows := by
  apply fullGraph_of_indexed_rows g fuel e rows he hsize
  intro i
  have hr : i.val < rows.size := by simpa [← hsize] using i.isLt
  exact indexedRowCheck_sound e rows i.val i.isLt hr (hchecks i.val i.isLt)

/-- Empty or mismatched arrays cannot certify an out-of-bounds row. -/
example : indexedRowCheck {} #[] 0 = false := by decide

end Shared.Beeping.NPcoNP.Grammar284
