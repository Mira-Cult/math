import Sude.FWWheelWitnessTraceStock

/-! Source first-wheel candidates after the same supplied early witnesses and
supplied growth trace. Numeric WW4, early-stop and floor conditions remain
explicit; this does not construct or append a growth stage. -/
namespace Sude
noncomputable section

/-- Use the actual trace's final pool and exact stock accounting to obtain
at least `6Q` disjoint equal-gap candidates for the first FW wheel. `R` is
a supplied certified lower radius bounded by the actual trace radius `last`.
The explicit numerical hypotheses do not assert trace or recipe existence. -/
theorem fw_wheel_trace_first_window_candidates {n : ℕ} (hn : 13 ≤ n * n)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (radius last : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      radius final last stages)
    (R : ℕ) (L m mf eta qbar : ℝ)
    (hR : 0 < R) (heven : 2 ∣ R) (hRlast : R ≤ last) (hL : 0 < L)
    (hnotdone : (last : ℝ) < (poolMaximum n : ℝ) / L)
    (hmf : 0 ≤ mf) (hm : mf ≤ m) (heta : 0 ≤ eta)
    (heps : 0 ≤ 1 / (2 * (1 + 1 / L)) - eta)
    (hmBound : m ≤ (((n * n : ℕ) : ℝ) - 13 - fwEarlyBudget n -
      2 * ((6 * (n + 8) : ℕ) : ℝ) * stages.length) / (poolMaximum n : ℝ))
    (hA : 0 ≤ eta * m * R - 1 / 2)
    (hq : ((6 * (n + 8) : ℕ) : ℝ) ≤ qbar * (poolMaximum n : ℝ))
    (hquota : 2 * (1 / (2 * (1 + 1 / L)) - eta) * mf ^ 2 ≥ 2 * (6 : ℝ) * qbar) :
    let Q := 6 * (n + 8)
    let P := sameClassPairs final (progressionBinKey 0 R 2)
    let T := ⌊eta * m * R - 1 / 2⌋₊
    let k := fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
      (Nat.totient_pos.mpr (by decide))
    let h := 2 * min k (R / 2)
    ∃ (gap : ℕ) (selected : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ h ≤ gap ∧ gap ≤ R ∧ gap ≤ last ∧
      6 * Q ≤ selected.card ∧
      (∀ p ∈ selected, (p, p + gap) ∈ P) ∧
      pairFootprint selected gap ⊆ final ∧
      Disjoint (pairFootprint selected gap)
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) ∧
      PairwiseDisjointPairs selected gap := by
  dsimp only
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hRlastR : (R : ℝ) ≤ last := by exact_mod_cast hRlast
  have hbefore : (R : ℝ) ≤ (poolMaximum n : ℝ) / L := by linarith
  have hscreen := fw_wheel_witness_trace_screened_units batches candidates hcard kept hsub blocks
    radius last final stages trace
  have hS : ∀ p ∈ final, (p : ℝ) ≤ poolMaximum n ∧ p % 2 = 1 ∧ Nat.Coprime p 15015 := by
    intro p hp
    have h := hscreen p hp
    exact ⟨h.2.2.2.2, h.2.2.1, h.2.2.2.1⟩
  have hactual := fw_wheel_witness_trace_normalized_stock hn batches hvalid candidates hcard kept hsub
    hkept hinj blocks hblocks radius last final stages trace
  have hbound := mul_le_mul_of_nonneg_right hmBound hX.le
  have hstock : m * (poolMaximum n : ℝ) ≤ (final.card : ℝ) := hbound.trans hactual
  obtain ⟨gap, selected, hgap, hdiv, hmin, hmax, hnum, hpairs, havail, hmatch⟩ :=
    fw_wheel_ww5_common_gap_from_bins final 15015 R 6 (6 * (n + 8))
      (poolMaximum n) L m mf eta qbar (by decide) (by decide) hR heven
      (by omega) hX hL hbefore hS hmf hm heta heps hstock hA hq hquota
  have hfoot : pairFootprint selected gap ⊆ final := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (havail p hp).1
    · obtain ⟨q, hq', rfl⟩ := Finset.mem_image.mp hp
      exact (havail q hq').2
  have hav : Disjoint (pairFootprint selected gap)
      (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) := by
    apply Finset.disjoint_left.mpr
    intro p hp hearly
    have hinit := trace.final_accounting.1 (hfoot hp)
    exact (Finset.mem_sdiff.mp hinit).2 hearly
  exact ⟨gap, selected, hgap, hdiv, hmin, hmax, hmax.trans hRlast, hnum, hpairs,
    hfoot, hav, hmatch⟩

end
end Sude
