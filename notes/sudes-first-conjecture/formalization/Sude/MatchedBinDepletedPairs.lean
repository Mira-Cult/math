import Sude.MatchedBinDepletion

/-! FW8: combine shared depletion with the repeated-gap square gate. -/
namespace Sude
noncomputable section

/-- A shared deletion set is paid once across disjoint low/high bins. If the
remaining guaranteed matched stock passes the square gate, two surviving
matched-bin cross-pairs have one gap and four distinct endpoints. -/
theorem matched_bins_repeated_after_deletion {N W : ℕ}
    (low high : Fin N → Finset ℕ) (removed differences : Finset ℕ)
    (hdis : (Set.univ : Set (Fin N × Bool)).PairwiseDisjoint
      (fun k => if k.2 then high k.1 else low k.1))
    (hlow : ∀ i, W ≤ (low i).card) (hhigh : ∀ i, W ≤ (high i).card)
    (horder : ∀ i j a, a ∈ low i → ∀ b, b ∈ high j → a < b)
    (hdiff : ∀ i a, a ∈ low i → ∀ b, b ∈ high i → b - a ∈ differences)
    (hgate : (N : ℝ) * differences.card < ((N * W - removed.card : ℕ) : ℝ) ^ 2) :
    ∃ b : DoublePair,
      (∃ i, b.low₁ ∈ low i \ removed ∧ b.high₁ ∈ high i \ removed) ∧
      (∃ j, b.low₂ ∈ low j \ removed ∧ b.high₂ ∈ high j \ removed) ∧
      b.low₁ ≠ b.low₂ ∧ b.high₁ ≠ b.high₂ ∧ b.low₁ < b.high₁ ∧
      b.low₂ < b.high₂ ∧ b.low₁ < b.high₂ ∧ b.low₂ < b.high₁ ∧
      b.high₁ - b.low₁ = b.high₂ - b.low₂ := by
  classical
  have hstock := matched_bin_stock_after_deletion low high removed hdis hlow hhigh
  have hnat : N * W - removed.card ≤
      ∑ i, min ((low i \ removed).card) ((high i \ removed).card) := by omega
  have hreal : ((N * W - removed.card : ℕ) : ℝ) ≤
      ((∑ i, min ((low i \ removed).card) ((high i \ removed).card) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hnon : 0 ≤ ((N * W - removed.card : ℕ) : ℝ) := by positivity
  have hsquare : ((N * W - removed.card : ℕ) : ℝ) ^ 2 ≤
      ((∑ i, min ((low i \ removed).card) ((high i \ removed).card) : ℕ) : ℝ) ^ 2 := by nlinarith
  apply matched_bins_repeated_difference (fun i => low i \ removed) (fun i => high i \ removed) differences
  · intro i j hij
    apply Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset
    apply hdis (show (i, false) ∈ (Set.univ : Set (Fin N × Bool)) by simp)
      (show (j, false) ∈ (Set.univ : Set (Fin N × Bool)) by simp)
    intro heq
    exact hij (congrArg Prod.fst heq)
  · intro i j a ha b hb
    exact horder i j a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1
  · intro i a ha b hb
    exact hdiff i a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1
  · exact hgate.trans_le hsquare

end
end Sude
