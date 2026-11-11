import Sude.FWActualSeed
import Sude.NarrowSeedPhysical

/-! NS1–NS4 applied to FW's actual selected candidate pairs. -/
namespace Sude
noncomputable section

/-- Conditional on the finite twin-prime population and bridge window, FW's
sixteen retained groups have the source variance invoice. All candidate-pair
endpoints, hence all retained endpoints, are distinct available pool values.
The probabilistic allocation and finite population remain separate goals. -/
theorem fw_actual_narrow_seed (lower : RSIndexLower) (n : ℕ)
    (seeds bridges : Finset ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hbridge : ∀ p ∈ bridges, poolMaximum n ≤ 4 * p)
    (hcount : 3650551 ≤ seeds.card) :
    let Q := 6 * (n + 8)
    let r := 16 + 2 - 1
    ∃ (candidates : Finset ℕ) (hcard : candidates.card = r * Q),
      candidates ⊆ seeds ∧
      let w := sortedSeedReal candidates r Q hcard
      ∃ kept : Finset ℕ, kept ⊆ Finset.range r ∧ kept.card = 16 ∧
        (∃ z : ℝ, (∃ i ∈ kept, z = w (i * Q + (Q - 1)) - w (i * Q)) ∧
          (∀ i ∈ kept, w (i * Q + (Q - 1)) - w (i * Q) ≤ z) ∧
          3 * 6 * (∑ i ∈ kept, (w (i * Q + (Q - 1)) - w (i * Q)) ^ 2) + 4 * z ^ 2 ≤
            (11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2) ∧
        Function.Injective (sortedSeedEndpoint candidates r Q 2 hcard) ∧
        ∀ x, sortedSeedEndpoint candidates r Q 2 hcard x ∈ poolFinset n \ bridges := by
  dsimp only
  let Q := 6 * (n + 8)
  let r := 16 + 2 - 1
  obtain ⟨candidates, hsub, hcard0, hmatch, hav, _⟩ :=
    fw_actual_seed_candidates_after_bridges lower n seeds bridges hnlo hnhi
      hseed hprime hbridge hcount
  have hcard : candidates.card = r * Q := by simpa [r, Q, Nat.mul_comm] using hcard0
  have hQ : 0 < Q := by dsimp [Q]; omega
  have hB : ∀ p ∈ candidates, p ≤ 2 ^ 30 := by
    intro p hp
    have h := hseed p (hsub hp)
    omega
  have hv := sortedSeedCandidates_variance candidates (poolFinset n) bridges Q 16 2 2
    (2 ^ 30) 6 hQ (by decide) (by decide) (by decide) (by norm_num)
    hcard hB hmatch hav
  refine ⟨candidates, hcard, hsub, ?_⟩
  norm_num at hv ⊢
  exact hv

end
end Sude
