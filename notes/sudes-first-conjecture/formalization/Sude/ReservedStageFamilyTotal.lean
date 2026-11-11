import Sude.ReservedPoolMean

/-! Exact total accounting for supplied pairwise-disjoint physical stages.
The actual construction's disjointness, counts and midpoint means are inputs. -/
namespace Sude
noncomputable section

/-- A physical stage union has the supplied total cardinality and its signed
deviation is the sum of the stage deviations. Empty stage sets are allowed. -/
theorem reserved_stage_family_signed_total {n : ℕ} {I : Type*} [DecidableEq I]
    (a : Cell n ≃ Fin (n * n)) (stages : Finset I)
    (cells : I → Finset (Cell n)) (count : I → ℕ) (mean : I → ℝ)
    (hdis : Set.PairwiseDisjoint (↑stages : Set I) cells)
    (hcard : ∀ j ∈ stages, (cells j).card = count j)
    (hsum : ∀ j ∈ stages, (∑ z ∈ cells j, (entry a z : ℝ)) = (count j : ℝ) * mean j)
    (μ : ℝ) :
    (stages.biUnion cells).card = ∑ j ∈ stages, count j ∧
    (∑ z ∈ stages.biUnion cells, (entry a z : ℝ)) -
        ((stages.biUnion cells).card : ℝ) * μ =
      ∑ j ∈ stages, (count j : ℝ) * (mean j - μ) := by
  classical
  have hc : (stages.biUnion cells).card = ∑ j ∈ stages, count j := by
    rw [Finset.card_biUnion hdis]
    exact Finset.sum_congr rfl hcard
  have hv : (∑ z ∈ stages.biUnion cells, (entry a z : ℝ)) =
      ∑ j ∈ stages, (count j : ℝ) * mean j := by
    rw [Finset.sum_biUnion hdis]
    exact Finset.sum_congr rfl hsum
  refine ⟨hc, ?_⟩
  rw [hv, hc, Nat.cast_sum]
  rw [Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- For uniform stage size `2d(n+8)`, the signed deviation has the exact
family coefficient required by the signed unused-pool cancellation. -/
theorem reserved_uniform_stage_family_signed_total {n : ℕ} {I : Type*} [DecidableEq I]
    (a : Cell n ≃ Fin (n * n)) (stages : Finset I)
    (cells : I → Finset (Cell n)) (d : ℕ) (mean : I → ℝ)
    (hdis : Set.PairwiseDisjoint (↑stages : Set I) cells)
    (hcard : ∀ j ∈ stages, (cells j).card = 2 * d * (n + 8))
    (hsum : ∀ j ∈ stages,
      (∑ z ∈ cells j, (entry a z : ℝ)) = (2 * d * (n + 8) : ℕ) * mean j) :
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    (stages.biUnion cells).card = stages.card * (2 * d * (n + 8)) ∧
    (∑ z ∈ stages.biUnion cells, (entry a z : ℝ)) -
        ((stages.biUnion cells).card : ℝ) * μ =
      2 * (d : ℝ) * ((n : ℝ) + 8) * ∑ j ∈ stages, (mean j - μ) := by
  dsimp only
  have h := reserved_stage_family_signed_total a stages cells (fun _ => 2 * d * (n + 8))
    mean hdis hcard hsum (centralEntriesMean (prescribedPoolValues n) centralPoolValue)
  constructor
  · simpa using h.1
  · rw [h.2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    push_cast
    ring

end
end Sude
