import Sude.DoubleBlockScoreDecomposition
import Sude.FiniteMomentSelection

/-! Two-sided finite selection for the midpoint scores of supplied source
blocks. The failure budget and source intervals are explicit inputs. No
physical square, geometric packing, numerical estimate or grid is constructed. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory

local instance doubleBlockSelectionPermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- The centered permutation component for a single labelled line. -/
def doubleBlockStageScore {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Cell n → Prop) (old : Cell n ≃ Fin (n * n))
    (π : Fin P → Equiv.Perm (Fin B)) : ℝ :=
  ∑ j, stageWeightedCentered (fun _ => Finset.univ) (doubleBlockLineWeight cells line)
    (doubleBlockMidpoint cells old) j (π j)

/-- The sampled weighted midpoint sum, centered at each stage's actual source
mean. One shared Boolean swaps the pair positions in each destination block. -/
def doubleBlockSampleScore {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Cell n → Prop) (old : Cell n ≃ Fin (n * n))
    (π : Fin P → Equiv.Perm (Fin B)) (s : (Fin P × Fin B) → Bool) : ℝ :=
  ∑ j, ∑ b,
    (fairBlockSwapValue (doubleBlockPairMidpoint cells old j (π j b) 0)
      (doubleBlockPairMidpoint cells old j (π j b) 1)
      (physicalPairLineWeight cells line (j,b,0)) (physicalPairLineWeight cells line (j,b,1)) (s (j,b)) -
      doubleBlockLineWeight cells line j b * doubleStageMidpointMean cells old j)

/-- Exact sampled-score decomposition using the actual stage means. -/
theorem double_block_sample_score_decomposition {n P B : ℕ} (hB : 0 < B)
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Cell n → Prop) (old : Cell n ≃ Fin (n * n))
    (π : Fin P → Equiv.Perm (Fin B)) (s : (Fin P × Fin B) → Bool) :
    doubleBlockSampleScore cells line old π s = doubleBlockStageScore cells line old π +
      ∑ j, ∑ b, (fairBlockSwapValue (doubleBlockPairMidpoint cells old j (π j b) 0)
        (doubleBlockPairMidpoint cells old j (π j b) 1)
        (physicalPairLineWeight cells line (j,b,0)) (physicalPairLineWeight cells line (j,b,1)) (s (j,b)) -
        doubleBlockLineWeight cells line j b * doubleBlockMidpoint cells old j (π j b)) := by
  classical
  unfold doubleBlockSampleScore doubleBlockStageScore
  have hstage (j : Fin P) : stageWeightedCentered (fun _ => Finset.univ)
      (doubleBlockLineWeight cells line) (doubleBlockMidpoint cells old) j (π j) =
      ∑ b, doubleBlockLineWeight cells line j b *
        (doubleBlockMidpoint cells old j (π j b) - doubleStageMidpointMean cells old j) := by
    rw [stageWeightedCentered_eq_explicit_mean hB]
    simp only [doubleStageMidpointMean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp_rw [hstage]
  simp only [Finset.sum_sub_distrib, mul_sub]
  ring

/-- Use the same source values for both signs, negating both weights and the
outer score in the lower-tail event. -/
def doubleBlockSign (positive : Bool) (x : ℝ) : ℝ := if positive then x else -x

/-- The centered fair-swap expression is linear under simultaneous negation
of its two weights. -/
theorem double_block_signed_swap (positive flip : Bool) (x y w₁ w₂ : ℝ) :
    doubleBlockSign positive (fairBlockSwapValue x y w₁ w₂ flip - (w₁+w₂)*(x+y)/2) =
      fairBlockSwapValue x y (doubleBlockSign positive w₁) (doubleBlockSign positive w₂) flip -
        (doubleBlockSign positive w₁ + doubleBlockSign positive w₂)*(x+y)/2 := by
  cases positive <;> cases flip <;> simp [doubleBlockSign, fairBlockSwapValue] <;> ring


/-- The explicit product of the one-block bounds for one sign and line. -/
def doubleBlockSignedSwapBound {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Cell n → Prop) (lo hi : Fin P → ℝ) (t : ℝ) (positive : Bool) : ℝ :=
  ∏ i : Fin P × Fin B, Real.exp (t ^ 2 *
    ((doubleBlockSign positive (physicalPairLineWeight cells line (i.1,i.2,0)) -
      doubleBlockSign positive (physicalPairLineWeight cells line (i.1,i.2,1))) ^ 2 *
      (hi i.1 - lo i.1) ^ 2 / 4) / 2)

/-- Under supplied source-midpoint intervals and an exact two-sided Chernoff
budget, one permutation and one shared swap vector make every sampled
midpoint score strictly small. The budget keeps the actual positive and
negative outer MGFs; no bound on them or on physical line weights is assumed. -/
theorem double_block_simultaneous_sample_exists {n P B : ℕ} {L : Type*} [Fintype L]
    (hB : 0 < B) (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : L → Cell n → Prop) (old : Cell n ≃ Fin (n * n))
    (lo hi : Fin P → ℝ) (threshold t : L → ℝ)
    (ht : ∀ l, 0 ≤ t l)
    (hinterval : ∀ j b p, doubleBlockPairMidpoint cells old j b p ∈ Set.Icc (lo j) (hi j))
    (hbudget : (∑ l, ∑ positive : Bool, Real.exp (-t l * threshold l) *
      (mgf (fun π => doubleBlockSign positive (doubleBlockStageScore cells (line l) old π))
        (stagePermutationMeasure P B) (t l) *
        doubleBlockSignedSwapBound cells (line l) lo hi (t l) positive)) < 1) :
    ∃ π s, ∀ l, |doubleBlockSampleScore cells (line l) old π s| < threshold l := by
  classical
  apply stage_fair_swap_simultaneous_exists P B
    (fun l π s => doubleBlockSampleScore cells (line l) old π s)
    (fun l positive π => doubleBlockSign positive (doubleBlockStageScore cells (line l) old π))
    (fun _ _ π i => doubleBlockPairMidpoint cells old i.1 (π i.1 i.2) 0)
    (fun _ _ π i => doubleBlockPairMidpoint cells old i.1 (π i.1 i.2) 1)
    (fun l positive i => doubleBlockSign positive (physicalPairLineWeight cells (line l) (i.1,i.2,0)))
    (fun l positive i => doubleBlockSign positive (physicalPairLineWeight cells (line l) (i.1,i.2,1)))
    (fun _ _ i => lo i.1) (fun _ _ i => hi i.1) threshold t ht
  · intro l positive π i
    exact hinterval i.1 (π i.1 i.2) 0
  · intro l positive π i
    exact hinterval i.1 (π i.1 i.2) 1
  · intro l positive π s
    rw [double_block_sample_score_decomposition hB cells (line l) old π s]
    cases positive
    · simp only [doubleBlockSign, Bool.false_eq_true, ↓reduceIte, Fintype.sum_prod_type, neg_add,
        ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro b _
      unfold doubleBlockLineWeight doubleBlockMidpoint
      cases s (j,b) <;> simp [fairBlockSwapValue] <;> ring
    · simp only [doubleBlockSign, ↓reduceIte, Fintype.sum_prod_type]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro b _
      unfold doubleBlockLineWeight doubleBlockMidpoint
      ring
  · exact hbudget


end
end Sude
