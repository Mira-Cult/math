import Sude.MatchedBinBatch

/-! Install FW matched-bin blocks into supplied distinct physical cells. -/
namespace Sude
noncomputable section

/-- The matched-bin gate selects a disjoint sequence of actual pool entries
and installs it into supplied disjoint cells, preserving reserved cells. The
caller must prove the bin supplies, numeric gate, and physical cell geometry. -/
theorem select_and_install_matched_bin_blocks {n N W B X k : ℕ}
    (low high : Fin N → Finset ℕ) (removed differences : Finset ℕ)
    (hdis : (Set.univ : Set (Fin N × Bool)).PairwiseDisjoint
      (fun z => if z.2 then high z.1 else low z.1))
    (hlow : ∀ i, W ≤ (low i).card) (hhigh : ∀ i, W ≤ (high i).card)
    (horder : ∀ i j a, a ∈ low i → ∀ b, b ∈ high j → a < b)
    (hdiff : ∀ i a, a ∈ low i → ∀ b, b ∈ high i → b - a ∈ differences)
    (hspan : differences.card ≤ X)
    (hgate : (N : ℝ) * X < ((N * W - B : ℕ) : ℝ) ^ 2)
    (hbudget : removed.card + 4 * k ≤ B)
    (hpoolLow : ∀ i p, p ∈ low i → p ∈ pool n)
    (hpoolHigh : ∀ i p, p ∈ high i → p ∈ pool n)
    (a : Cell n ≃ Fin (n * n)) (cells : Fin k × Fin 4 → Cell n)
    (reserved : Finset (Cell n)) (hcells : Function.Injective cells)
    (hnew : ∀ x, cells x ∉ reserved)
    (hreserved : ∀ c ∈ reserved, entry a c ∈ removed) :
    ∃ (blocks : List DoublePair) (hlen : blocks.length = k) (a' : Cell n ≃ Fin (n * n)),
      (∀ b ∈ blocks, b.valid (Finset.univ.biUnion low) (Finset.univ.biUnion high)) ∧
      blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint) ∧
      (∀ b ∈ blocks, Disjoint b.footprint removed) ∧
      (∀ x : Fin blocks.length × Fin 4,
        entry a' (cells (Fin.cast hlen x.1, x.2)) = doublePairSequenceEndpoint blocks x) ∧
      (∀ c ∈ reserved, entry a' c = entry a c) := by
  classical
  obtain ⟨blocks, hlen, hvalid, hpair, havoid⟩ :=
    select_matched_bin_double_pairs low high removed differences hdis hlow hhigh horder hdiff hspan hgate hbudget
  have horder' : ∀ p ∈ Finset.univ.biUnion low, ∀ q ∈ Finset.univ.biUnion high, p < q := by
    intro p hp q hq
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hq
    exact horder i j p hi q hj
  have hpoolL : ∀ p ∈ Finset.univ.biUnion low, p ∈ pool n := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    exact hpoolLow i p hi
  have hpoolH : ∀ p ∈ Finset.univ.biUnion high, p ∈ pool n := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    exact hpoolHigh i p hi
  let cells' : Fin blocks.length × Fin 4 → Cell n := fun x => cells (Fin.cast hlen x.1, x.2)
  have hcells' : Function.Injective cells' := by
    rintro ⟨i, u⟩ ⟨j, v⟩ h
    have he : (Fin.cast hlen i, u) = (Fin.cast hlen j, v) := hcells h
    have hi : i = j := Fin.ext (congrArg (fun z : Fin k × Fin 4 => z.1.val) he)
    have hv : u = v := congrArg Prod.snd he
    cases hi
    cases hv
    rfl
  have hnew' : ∀ x, cells' x ∉ reserved := fun x => hnew (Fin.cast hlen x.1, x.2)
  have havoidentries : ∀ b ∈ blocks, ∀ v ∈ b.footprint, ∀ c ∈ reserved, v ≠ entry a c := by
    intro b hb v hv c hc heq
    exact Finset.disjoint_left.mp (havoid b hb) hv (heq ▸ hreserved c hc)
  obtain ⟨a', hplace, hfixed⟩ := install_double_pair_sequence blocks _ _ horder' hvalid hpair
    hpoolL hpoolH a cells' reserved hcells' hnew' havoidentries
  exact ⟨blocks, hlen, a', hvalid, hpair, havoid, hplace, hfixed⟩

end
end Sude
