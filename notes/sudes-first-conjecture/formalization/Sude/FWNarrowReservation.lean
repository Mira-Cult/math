import Sude.FWNarrowSeed
import Sude.NarrowSeedRetained

/-! FW's narrowed seed groups with exact physical reservations. -/
namespace Sude
noncomputable section

/-- FW's selected groups have the source width invoice, reserve exactly
`2 * Q * 16` genuine distinct pool entries, and leave every discarded
candidate endpoint available after bridge and seed reservations. The finite
twin-prime population and probabilistic allocation remain open. -/
theorem fw_actual_narrow_seed_reservation (lower : RSIndexLower) (n : ℕ)
    (seeds bridges : Finset ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hbridge : ∀ p ∈ bridges, poolMaximum n ≤ 4 * p)
    (hcount : 3650551 ≤ seeds.card) :
    let Q := 6 * (n + 8)
    let r := 16 + 2 - 1
    ∃ (candidates : Finset ℕ) (hcard : candidates.card = r * Q),
      candidates ⊆ seeds ∧
      ∃ (kept : Finset ℕ) (hsub : kept ⊆ Finset.range r), kept.card = 16 ∧
        (let w := sortedSeedReal candidates r Q hcard
         ∃ z : ℝ, (∃ i ∈ kept, z = w (i * Q + (Q - 1)) - w (i * Q)) ∧
          (∀ i ∈ kept, w (i * Q + (Q - 1)) - w (i * Q) ≤ z) ∧
          3 * 6 * (∑ i ∈ kept, (w (i * Q + (Q - 1)) - w (i * Q)) ^ 2) + 4 * z ^ 2 ≤
            (11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2) ∧
        (let R := retainedSeedEndpoints candidates r Q 2 hcard kept hsub
         R.card = 2 * Q * 16 ∧ R ⊆ poolFinset n \ bridges ∧
         ∀ x, x.1.1.val ∉ kept →
           sortedSeedEndpoint candidates r Q 2 hcard x ∈ poolFinset n \ (bridges ∪ R)) := by
  dsimp only
  let Q := 6 * (n + 8)
  let r := 16 + 2 - 1
  obtain ⟨candidates, hcard, hcand, kept, hsub, hkept, hvariance, hinj, havail⟩ :=
    fw_actual_narrow_seed lower n seeds bridges hnlo hnhi hseed hprime hbridge hcount
  refine ⟨candidates, hcard, hcand, kept, hsub, hkept, hvariance, ?_⟩
  let R := retainedSeedEndpoints candidates r Q 2 hcard kept hsub
  have hRcard : R.card = 2 * Q * 16 := by
    dsimp [R, retainedSeedEndpoints]
    rw [Finset.card_image_of_injective _ hinj, retainedSeedLabels_card, hkept]
  have hRsub : R ⊆ poolFinset n \ bridges := by
    intro p hp
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
    exact havail x
  refine ⟨hRcard, hRsub, ?_⟩
  intro x hdiscard
  have hx := Finset.mem_sdiff.mp (havail x)
  have hnot := discardedSeedEndpoint_not_retained candidates r Q 2 hcard hinj kept hsub x hdiscard
  refine Finset.mem_sdiff.mpr ⟨hx.1, ?_⟩
  intro hm
  rcases Finset.mem_union.mp hm with hb | hret
  · exact hx.2 hb
  · exact hnot hret

end
end Sude
