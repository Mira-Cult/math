import Sude.FWGrowthNarrowPD2
import Sude.BTGrowingPermutedPlacement

/-! Exact midpoint, gap and injectivity consequences of a growth-trace
placement on the supplied square. No allocation or line bound is asserted. -/
namespace Sude
noncomputable section

/-- A placement whose entries are the permuted trace endpoints has distinct
physical cells, the stage's actual common gap, and the midpoint of the
corresponding permuted low label, all on the same square. -/
theorem growth_permuted_trace_midpoints
    {n P Q g : ℕ} {initial final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage} (trace : BTGrowingTrace g Q initial radius final last stages)
    (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (cells : (Fin P × Fin Q) × Bool → Cell n) (a : Cell n ≃ Fin (n*n))
    (ω : Fin P → Equiv.Perm (Fin Q))
    (hplaced : ∀ x, entry a (cells x) =
      (trace.poolValues hlen hpool (stagePairPermutation ω x)).val) :
    Function.Injective cells ∧
    (∀ j i, entry a (cells ((j,i),true)) = entry a (cells ((j,i),false)) +
      (BTStageTrace.stageAt stages hlen j).gap) ∧
    (∀ j i, (((entry a (cells ((j,i),false)) : ℝ) +
      (entry a (cells ((j,i),true)) : ℝ)) / 2) =
      growthStageMidpoint (BTStageTrace.stageAt stages hlen j) (trace.lowAt hlen j (ω j i))) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x y heq
    apply (stagePairPermutation ω).injective
    apply trace.poolValues_injective hlen hpool
    apply Subtype.ext
    rw [← hplaced x, ← hplaced y, heq]
  · intro j i
    rw [hplaced, hplaced]
    exact trace.poolValues_gap hlen hpool j (ω j i)
  · intro j i
    rw [hplaced, hplaced]
    simp [BTGrowingTrace.poolValues, stagePairPermutation, growthStageMidpoint]

end
end Sude
