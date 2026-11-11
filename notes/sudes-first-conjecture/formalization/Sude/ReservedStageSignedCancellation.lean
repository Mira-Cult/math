import Sude.ReservedStageFamilyTotal
import Sude.ReservedFamilySignedCancellation

/-! Signed unused-pool cancellation for supplied disjoint physical stages.
The physical construction, reservation and line counts remain hypotheses. -/
namespace Sude
noncomputable section

/-- The supplied uniform stage totals give the exact family deviation used by
the physical unused-pool cancellation; the actual remainder remains signed. -/
theorem actual_reserved_stages_signed_cancellation {n : ℕ} {I : Type*} [DecidableEq I]
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (stages : Finset I) (cells : I → Finset (Cell n)) (d r q br : ℕ) (mean : I → ℝ)
    (hdis : Set.PairwiseDisjoint (↑stages : Set I) cells)
    (hcard : ∀ j ∈ stages, (cells j).card = 2 * d * (n + 8))
    (hsum : ∀ j ∈ stages,
      (∑ z ∈ cells j, (entry a z : ℝ)) = (2 * d * (n + 8) : ℕ) * mean j)
    (hsub : stages.biUnion cells ⊆ reserved)
    (hreservedCard : reserved.card = r * (n + 8) + br)
    (hreserved : reserved.card < n * n) (hline : r + q ≤ n) :
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let A : ℝ := ∑ j ∈ stages, (mean j - μ)
    let other : ℝ := (∑ z ∈ reserved \ stages.biUnion cells, (entry a z : ℝ)) -
      ((reserved \ stages.biUnion cells).card : ℝ) * μ
    let N : ℝ := (n * n - (r * (n + 8) + br) : ℕ)
    let k : ℝ := (n - r - q : ℕ)
    2 * (d : ℝ) * A + k *
        (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - μ) =
      (2 * (d : ℝ) * A / N) * (((n : ℝ) + 8) * (q : ℝ) - br - 8 * n) -
        k * other / N := by
  classical
  have htotal := reserved_uniform_stage_family_signed_total a stages cells d mean hdis hcard hsum
  dsimp only at htotal ⊢
  have hdev :
      (∑ z ∈ stages.biUnion cells, (entry a z : ℝ)) -
          ((stages.card * (2 * d * (n + 8)) : ℕ) : ℝ) *
            centralEntriesMean (prescribedPoolValues n) centralPoolValue =
        2 * (d : ℝ) * ((n : ℝ) + 8) *
          ∑ j ∈ stages, (mean j - centralEntriesMean (prescribedPoolValues n) centralPoolValue) := by
    rw [← htotal.1]
    exact htotal.2
  exact actual_reserved_family_signed_cancellation a reserved (stages.biUnion cells)
    d r q br (stages.card * (2 * d * (n + 8)))
    (∑ j ∈ stages, (mean j - centralEntriesMean (prescribedPoolValues n) centralPoolValue))
    hsub htotal.1 hreservedCard hreserved hline hdev

end
end Sude
