import Sude.FWInstalledBlockGeometry

/-! Actual FW rectangle gaps have the source's positive even sub-X range. -/
namespace Sude
noncomputable section

/-- For each supplied matched block installed in the given cells, its two
oppositely oriented physical pairs share one positive even natural gap. That
gap lies in `[2X/3, X)`. Parity follows from the prescribed pool entries, and
the bounds follow from matched-bin geometry. No stock or routing conclusion
is asserted. -/
theorem fw_installed_matched_block_even_gap {n : ℕ}
    (m X : ℝ) (hX : 100 ≤ X)
    (hmlo : (243 / 500 : ℝ) * X ≤ m) (hmhi : m ≤ (123 / 250 : ℝ) * X)
    (blocks : List DoublePair) (a : Cell n ≃ Fin (n * n))
    (cells : Fin blocks.length × Fin 4 → Cell n)
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft m X) (fwReflectedRight m X))
      (bmorHighBins (fwReflectedLeft m X) (fwReflectedRight m X)))
    (hplaced : ∀ x, entry a (cells x) = doublePairSequenceEndpoint blocks x)
    (i : Fin blocks.length) :
    ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
      entry a (cells (i, 1)) = entry a (cells (i, 0)) + gap ∧
      entry a (cells (i, 2)) = entry a (cells (i, 3)) + gap ∧
      (2 / 3 : ℝ) * X ≤ (gap : ℝ) ∧ (gap : ℝ) < X := by
  have hvalid : ∀ b ∈ blocks, b.valid
      (Finset.univ.biUnion (bmorLowBins (fwReflectedLeft m X) (fwReflectedRight m X)))
      (Finset.univ.biUnion (bmorHighBins (fwReflectedLeft m X) (fwReflectedRight m X))) := by
    intro b hb
    exact (hmatched b hb).1
  obtain ⟨gap, hpos, hfirst, hsecond⟩ :=
    installed_double_pair_gaps blocks _ _ hvalid a cells hplaced i
  have hodd0 : Odd (entry a (cells (i, 0))) := oddPrime_odd _
  have hodd1 : Odd (entry a (cells (i, 1))) := oddPrime_odd _
  obtain ⟨u, hu⟩ := hodd0
  obtain ⟨v, hv⟩ := hodd1
  have heven : gap % 2 = 0 := by omega
  have hgeom := fw_installed_matched_block_bounds m X hX hmlo hmhi blocks a cells hmatched hplaced i
  have hgap : (entry a (cells (i, 1)) : ℝ) - entry a (cells (i, 0)) = (gap : ℝ) := by
    rw [hfirst]
    push_cast
    ring
  have hlower : (2 / 3 : ℝ) * X ≤ (gap : ℝ) := by linarith [hgeom.2.1]
  have hupper : (gap : ℝ) < X := by linarith [hgeom.2.2.1]
  exact ⟨gap, hpos, heven, hfirst, hsecond, hlower, hupper⟩

end
end Sude
