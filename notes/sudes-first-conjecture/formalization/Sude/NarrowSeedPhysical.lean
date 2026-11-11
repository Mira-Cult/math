import Sude.NarrowSeedSorted
import Sude.PrimePairMatching

/-! Actual candidate pairs in sorted equal-sized seed groups. -/
namespace Sude
noncomputable section

/-- The source's consecutive groups, indexed by group and slot. -/
def sortedSeedLower (candidates : Finset ℕ) (r Q : ℕ)
    (hcard : candidates.card = r * Q) (x : Fin r × Fin Q) : ℕ :=
  candidates.orderEmbOfFin hcard (finProdFinEquiv x)

theorem sortedSeedLower_mem (candidates : Finset ℕ) (r Q : ℕ)
    (hcard : candidates.card = r * Q) (x : Fin r × Fin Q) :
    sortedSeedLower candidates r Q hcard x ∈ candidates :=
  candidates.orderEmbOfFin_mem hcard (finProdFinEquiv x)

theorem sortedSeedLower_injective (candidates : Finset ℕ) (r Q : ℕ)
    (hcard : candidates.card = r * Q) :
    Function.Injective (sortedSeedLower candidates r Q hcard) :=
  (candidates.orderEmbOfFin hcard).injective.comp finProdFinEquiv.injective

/-- Both endpoints of every sorted pair remain genuine and globally distinct. -/
def sortedSeedEndpoint (candidates : Finset ℕ) (r Q gap : ℕ)
    (hcard : candidates.card = r * Q) (x : (Fin r × Fin Q) × Bool) : ℕ :=
  pairEndpoint candidates gap
    (⟨sortedSeedLower candidates r Q hcard x.1,
      sortedSeedLower_mem candidates r Q hcard x.1⟩, x.2)

theorem sortedSeedEndpoint_injective (candidates : Finset ℕ) (r Q gap : ℕ)
    (hcard : candidates.card = r * Q) (hgap : 0 < gap)
    (hmatch : PairwiseDisjointPairs candidates gap) :
    Function.Injective (sortedSeedEndpoint candidates r Q gap hcard) := by
  intro x y hxy
  have he := pairEndpoint_injective candidates gap hgap hmatch hxy
  have hlabels : sortedSeedLower candidates r Q hcard x.1 =
      sortedSeedLower candidates r Q hcard y.1 := congrArg (fun p => p.1.val) he
  have hindex : x.1 = y.1 := sortedSeedLower_injective candidates r Q hcard hlabels
  have hside : x.2 = y.2 := congrArg (fun p : {p // p ∈ candidates} × Bool => p.2) he
  exact Prod.ext hindex hside

/-- All endpoints in every sorted group avoid the pre-existing reservation
and belong to the supplied pool. -/
theorem sortedSeedEndpoint_available (candidates pool reserved : Finset ℕ)
    (r Q gap : ℕ) (hcard : candidates.card = r * Q)
    (havailable : pairFootprint candidates gap ⊆ pool \ reserved)
    (x : (Fin r × Fin Q) × Bool) :
    sortedSeedEndpoint candidates r Q gap hcard x ∈ pool \ reserved := by
  apply havailable
  rcases x with ⟨x, side⟩
  have hp := sortedSeedLower_mem candidates r Q hcard x
  cases side
  · apply Finset.mem_union_left
    simpa [sortedSeedEndpoint, pairEndpoint] using hp
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨_, hp, by simp [sortedSeedEndpoint, pairEndpoint]⟩

/-- Total real-valued enumeration; only indices below `r * Q` are used. -/
def sortedSeedReal (candidates : Finset ℕ) (r Q : ℕ)
    (hcard : candidates.card = r * Q) (i : ℕ) : ℝ :=
  if hi : i < r * Q then candidates.orderEmbOfFin hcard ⟨i, hi⟩ else 0

theorem sortedSeedReal_mono (candidates : Finset ℕ) (r Q : ℕ)
    (hcard : candidates.card = r * Q) :
    ∀ i j, i ≤ j → j < r * Q →
      sortedSeedReal candidates r Q hcard i ≤ sortedSeedReal candidates r Q hcard j := by
  intro i j hij hj
  have hi : i < r * Q := lt_of_le_of_lt hij hj
  have h := (candidates.orderEmbOfFin hcard).monotone
    (show (⟨i, hi⟩ : Fin (r * Q)) ≤ ⟨j, hj⟩ from hij)
  simpa [sortedSeedReal, hi, hj] using (show
    ((candidates.orderEmbOfFin hcard ⟨i, hi⟩ : ℕ) : ℝ) ≤
      (candidates.orderEmbOfFin hcard ⟨j, hj⟩ : ℕ) by exact_mod_cast h)

/-- A group slot is the actual candidate at its consecutive sorted rank. -/
theorem sortedSeedReal_slot (candidates : Finset ℕ) (r Q : ℕ)
    (hcard : candidates.card = r * Q) (j : Fin r) (i : Fin Q) :
    sortedSeedReal candidates r Q hcard (j.val * Q + i.val) =
      (sortedSeedLower candidates r Q hcard (j, i) : ℝ) := by
  have hindex : (finProdFinEquiv (j, i)).val = j.val * Q + i.val := by
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  have hi : j.val * Q + i.val < r * Q := by rw [← hindex]; exact (finProdFinEquiv (j, i)).isLt
  simp only [sortedSeedReal, dif_pos hi, sortedSeedLower]
  congr 2
  exact Fin.ext hindex.symm

/-- The NS4 width invoice applies to sorted groups of genuine candidates.
Distinct endpoints remain available throughout the entire selected family. -/
theorem sortedSeedCandidates_variance (candidates pool reserved : Finset ℕ)
    (Q s t gap B : ℕ) (d : ℝ) (hQ : 0 < Q) (hs : 0 < s) (ht : 2 ≤ t)
    (hgap : 0 < gap) (hd : 0 ≤ d)
    (hcard : candidates.card = (s + t - 1) * Q)
    (hB : ∀ p ∈ candidates, p ≤ B)
    (hmatch : PairwiseDisjointPairs candidates gap)
    (havailable : pairFootprint candidates gap ⊆ pool \ reserved) :
    let r := s + t - 1
    let w := sortedSeedReal candidates r Q hcard
    ∃ kept : Finset ℕ, kept ⊆ Finset.range r ∧ kept.card = s ∧
      (∃ z : ℝ, (∃ i ∈ kept, z = w (i * Q + (Q - 1)) - w (i * Q)) ∧
        (∀ i ∈ kept, w (i * Q + (Q - 1)) - w (i * Q) ≤ z) ∧
        3 * d * (∑ i ∈ kept, (w (i * Q + (Q - 1)) - w (i * Q)) ^ 2) + 4 * z ^ 2 ≤
          (3 * d / (4 * ((t : ℝ) - 1)) + 4 / (t : ℝ) ^ 2) * (B : ℝ) ^ 2) ∧
      Function.Injective (sortedSeedEndpoint candidates r Q gap hcard) ∧
      ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ pool \ reserved := by
  dsimp only
  let r := s + t - 1
  let w := sortedSeedReal candidates r Q hcard
  have hbound : ∀ i < r * Q, (0 : ℝ) ≤ w i ∧ w i ≤ B := by
    intro i hi
    have hp := candidates.orderEmbOfFin_mem hcard (⟨i, hi⟩ : Fin (r * Q))
    have hb := hB _ hp
    constructor
    · dsimp [w, sortedSeedReal]
      split <;> positivity
    · simpa [w, sortedSeedReal, hi] using (show
        ((candidates.orderEmbOfFin hcard ⟨i, hi⟩ : ℕ) : ℝ) ≤ (B : ℝ) by exact_mod_cast hb)
  have hv := sorted_seed_narrowest_variance w Q s t 0 B d hQ hs ht hd (by positivity)
    (sortedSeedReal_mono candidates r Q hcard) hbound
  obtain ⟨kept, hsub, hcard', z, hz, hmax, hvariance⟩ := hv
  refine ⟨kept, hsub, hcard', ⟨z, hz, hmax, ?_⟩,
    sortedSeedEndpoint_injective candidates r Q gap hcard hgap hmatch,
    sortedSeedEndpoint_available candidates pool reserved r Q gap hcard havailable⟩
  simpa using hvariance

end
end Sude
