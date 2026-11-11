import Sude.MatchedBinPairs

/-! FW8: pay a shared deleted set exactly once across disjoint bins. -/
namespace Sude
noncomputable section

/-- If all low and high bins are physically disjoint and each initially has
at least `W` entries, deleting a single set of entries reduces the total
matched stock by at most the cardinality of that set. -/
theorem matched_bin_stock_after_deletion {N W : ℕ}
    (low high : Fin N → Finset ℕ) (removed : Finset ℕ)
    (hdis : (Set.univ : Set (Fin N × Bool)).PairwiseDisjoint
      (fun k => if k.2 then high k.1 else low k.1))
    (hlow : ∀ i, W ≤ (low i).card) (hhigh : ∀ i, W ≤ (high i).card) :
    N * W ≤ (∑ i, min ((low i \ removed).card) ((high i \ removed).card)) + removed.card := by
  classical
  let stock : Fin N × Bool → Finset ℕ := fun k => if k.2 then high k.1 else low k.1
  have hinterdis : (↑(Finset.univ : Finset (Fin N × Bool)) : Set (Fin N × Bool)).PairwiseDisjoint
      (fun k => stock k ∩ removed) := by
    intro x _ y _ hxy
    apply Disjoint.mono (Finset.inter_subset_left) (Finset.inter_subset_left)
    exact hdis (by simp) (by simp) hxy
  let deleted := (Finset.univ : Finset (Fin N × Bool)).biUnion (fun k => stock k ∩ removed)
  have hdsub : deleted ⊆ removed := by
    intro x hx
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hk).2
  have hdel : (∑ i, ((low i ∩ removed).card + (high i ∩ removed).card)) ≤ removed.card := by
    have h := Finset.card_le_card hdsub
    have hcard : deleted.card = ∑ k : Fin N × Bool, (stock k ∩ removed).card := by
      simp [deleted, Finset.card_biUnion hinterdis]
    rw [hcard, Fintype.sum_prod_type] at h
    simpa [stock, Fintype.sum_bool, add_comm] using h
  have hper : ∀ i, W ≤ min ((low i \ removed).card) ((high i \ removed).card) +
      ((low i ∩ removed).card + (high i ∩ removed).card) := by
    intro i
    have hl := Finset.card_sdiff_add_card_inter (low i) removed
    have hh := Finset.card_sdiff_add_card_inter (high i) removed
    have hli := hlow i
    have hhi := hhigh i
    omega
  have hsum : N * W ≤
      (∑ i, min ((low i \ removed).card) ((high i \ removed).card)) +
      ∑ i, ((low i ∩ removed).card + (high i ∩ removed).card) := by
    calc
      N * W = ∑ _i : Fin N, W := by simp
      _ ≤ ∑ i : Fin N, (min ((low i \ removed).card) ((high i \ removed).card) +
          ((low i ∩ removed).card + (high i ∩ removed).card)) :=
        Finset.sum_le_sum (fun i _ => hper i)
      _ = _ := Finset.sum_add_distrib
  exact hsum.trans (Nat.add_le_add_left hdel _)

end
end Sude
