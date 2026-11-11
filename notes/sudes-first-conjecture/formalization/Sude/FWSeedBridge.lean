import Sude.FWFiniteGates
import Sude.PrimePairMatching

/-! FW2: finite seed endpoints survive the prior bridge reservation. -/
namespace Sude

/-- Every endpoint of a bounded gap-two seed is below every bridge entry
when the actual pool maximum is more than four times the seed bound and
bridges lie in the source's central window. -/
theorem fw_seed_bridge_disjoint (seeds bridges : Finset ℕ) (B X : ℕ)
    (hsep : 4 * B < X) (hseed : ∀ p ∈ seeds, p + 2 ≤ B)
    (hbridge : ∀ p ∈ bridges, X ≤ 4 * p) :
    Disjoint (pairFootprint seeds 2) bridges := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hb
  have hu : p ≤ B := by
    rcases Finset.mem_union.mp hp with hl | hu
    · have h := hseed p hl
      omega
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
      exact hseed q hq
  have h := hbridge p hb
  omega

/-- The exact FW candidate quota can be taken from the source's finite
matching after bridges have been reserved. Both physical endpoints remain
in the original pool and outside the bridge set; their matching and exact
endpoint count are preserved. The finite seed population is an explicit
hypothesis here, not a trusted import. -/
theorem fw_seed_candidates_after_bridges
    (pool seeds bridges : Finset ℕ) (n X : ℕ)
    (hn : n ≤ 35733) (hsep : 4 * 2 ^ 30 < X)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hbridge : ∀ p ∈ bridges, X ≤ 4 * p)
    (hpool : ∀ p ∈ seeds, p ∈ pool ∧ p + 2 ∈ pool)
    (hmatch : PairwiseDisjointPairs seeds 2)
    (hcount : 3650551 ≤ seeds.card) :
    ∃ candidates : Finset ℕ,
      candidates ⊆ seeds ∧ candidates.card = 6 * (n + 8) * (16 + 2 - 1) ∧
      PairwiseDisjointPairs candidates 2 ∧
      pairFootprint candidates 2 ⊆ pool \ bridges ∧
      (pairFootprint candidates 2).card = 2 * (6 * (n + 8) * (16 + 2 - 1)) := by
  classical
  have hquota := (fw_seed_quota_gate n hn).trans hcount
  obtain ⟨candidates, hsub, hcard⟩ := Finset.exists_subset_card_eq hquota
  have hm : PairwiseDisjointPairs candidates 2 := by
    intro p hp q hq hpq
    exact hmatch p (hsub hp) q (hsub hq) hpq
  have hdis := fw_seed_bridge_disjoint seeds bridges (2 ^ 30) X hsep hseed hbridge
  have hsubset : pairFootprint candidates 2 ⊆ pool \ bridges := by
    intro p hp
    have hpSeed : p ∈ pairFootprint seeds 2 := by
      rcases Finset.mem_union.mp hp with hl | hu
      · exact Finset.mem_union_left _ (hsub hl)
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hsub hq, rfl⟩)
    have hpPool : p ∈ pool := by
      rcases Finset.mem_union.mp hp with hl | hu
      · exact (hpool p (hsub hl)).1
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
        exact (hpool q (hsub hq)).2
    exact Finset.mem_sdiff.mpr ⟨hpPool, (Finset.disjoint_left.mp hdis) hpSeed⟩
  refine ⟨candidates, hsub, hcard, hm, hsubset, ?_⟩
  rw [pairFootprint_card candidates 2 (by decide) hm, hcard]

end Sude
