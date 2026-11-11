import Sude.DoubleBlockSimultaneousSelection
import Sude.MixedMomentLogBudget

/-! A positive-invoice log budget for the finite sampled double-block
midpoint scores. This does not construct physical geometry or prove a
numerical weight invoice. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory

local instance doubleBlockLogPermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- The sum of stage-permutation and independent shared-swap proxies. -/
def doubleBlockCombinedProxy {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Cell n → Prop) (lo hi : Fin P → ℝ) : ℝ :=
  ((stageWeightedProxy (fun _ => Finset.univ) (doubleBlockLineWeight cells line) lo hi : NNReal) : ℝ) +
    ∑ i : Fin P × Fin B,
      (physicalPairLineWeight cells line (i.1,i.2,0) -
        physicalPairLineWeight cells line (i.1,i.2,1)) ^ 2 * (hi i.1 - lo i.1) ^ 2 / 4

/-- The actual signed stage MGF and signed swap product are bounded by the
exponential of the combined stage and swap proxy. -/
theorem double_block_signed_moment_le_proxy {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Cell n → Prop) (old : Cell n ≃ Fin (n * n)) (lo hi : Fin P → ℝ)
    (hinterval : ∀ j b p, doubleBlockPairMidpoint cells old j b p ∈ Set.Icc (lo j) (hi j))
    (t : ℝ) (positive : Bool) :
    mgf (fun π => doubleBlockSign positive (doubleBlockStageScore cells line old π))
      (stagePermutationMeasure P B) t * doubleBlockSignedSwapBound cells line lo hi t positive ≤
      Real.exp (doubleBlockCombinedProxy cells line lo hi * t ^ 2 / 2) := by
  classical
  have hw : ∀ j b, b ∈ (Finset.univ : Finset (Fin B)) →
      0 ≤ doubleBlockLineWeight cells line j b := by
    intro j b _
    unfold doubleBlockLineWeight physicalPairLineWeight
    split_ifs <;> norm_num
  have hv : ∀ j b, doubleBlockMidpoint cells old j b ∈ Set.Icc (lo j) (hi j) := by
    intro j b
    have h0 := hinterval j b 0
    have h1 := hinterval j b 1
    unfold doubleBlockMidpoint
    constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]
  have hs := stageWeighted_hasSubgaussian (fun _ : Fin P => Finset.univ)
    (doubleBlockLineWeight cells line) (doubleBlockMidpoint cells old) lo hi hw hv
  have hm : mgf (fun π => doubleBlockSign positive (doubleBlockStageScore cells line old π))
      (stagePermutationMeasure P B) t ≤
      Real.exp (((stageWeightedProxy (fun _ => Finset.univ) (doubleBlockLineWeight cells line) lo hi : NNReal) : ℝ) * t ^ 2 / 2) := by
    cases positive
    · change mgf (-(fun π : Fin P → Equiv.Perm (Fin B) =>
        ∑ j, stageWeightedCentered (fun _ => Finset.univ) (doubleBlockLineWeight cells line)
          (doubleBlockMidpoint cells old) j (π j))) (stagePermutationMeasure P B) t ≤ _
      exact hs.neg.mgf_le t
    · simpa [doubleBlockSign, doubleBlockStageScore] using hs.mgf_le t
  have hswap : doubleBlockSignedSwapBound cells line lo hi t positive =
      Real.exp ((∑ i : Fin P × Fin B,
        (physicalPairLineWeight cells line (i.1,i.2,0) -
          physicalPairLineWeight cells line (i.1,i.2,1)) ^ 2 * (hi i.1 - lo i.1) ^ 2 / 4) * t ^ 2 / 2) := by
    unfold doubleBlockSignedSwapBound
    rw [← Real.exp_sum]
    congr 1
    calc
      _ = ∑ i : Fin P × Fin B, (t ^ 2 / 2) *
          ((physicalPairLineWeight cells line (i.1,i.2,0) -
            physicalPairLineWeight cells line (i.1,i.2,1)) ^ 2 * (hi i.1 - lo i.1) ^ 2 / 4) := by
        apply Finset.sum_congr rfl
        intro i _
        cases positive <;> simp only [doubleBlockSign, Bool.false_eq_true, ↓reduceIte] <;> ring
      _ = _ := by rw [← Finset.mul_sum]; ring
  rw [hswap]
  calc
    _ ≤ Real.exp (((stageWeightedProxy (fun _ => Finset.univ) (doubleBlockLineWeight cells line) lo hi : NNReal) : ℝ) * t ^ 2 / 2) *
          Real.exp ((∑ i : Fin P × Fin B,
            (physicalPairLineWeight cells line (i.1,i.2,0) -
              physicalPairLineWeight cells line (i.1,i.2,1)) ^ 2 * (hi i.1 - lo i.1) ^ 2 / 4) * t ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hm (le_of_lt (Real.exp_pos _))
    _ = _ := by rw [← Real.exp_add]; congr 1; unfold doubleBlockCombinedProxy; ring


/-- A supplied positive common invoice for the combined proxies implies one
simultaneous logarithmic midpoint allocation. The source intervals and the
invoice are hypotheses; no physical existence or numerical estimate follows. -/
theorem double_block_log_simultaneous_sample_exists {n P B m : ℕ}
    (hB : 0 < B) (hm : 0 < m) (V : ℝ) (hV : 0 < V)
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Fin m → Cell n → Prop) (old : Cell n ≃ Fin (n * n)) (lo hi : Fin P → ℝ)
    (hinterval : ∀ j b p, doubleBlockPairMidpoint cells old j b p ∈ Set.Icc (lo j) (hi j))
    (hinvoice : ∀ l, doubleBlockCombinedProxy cells (line l) lo hi ≤ V / 4) :
    ∃ π s, ∀ l, |doubleBlockSampleScore cells (line l) old π s| <
      Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2) := by
  classical
  let E := Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2)
  let t := 4 * E / V
  let moment : Fin m → Bool → ℝ := fun l positive =>
    mgf (fun π => doubleBlockSign positive (doubleBlockStageScore cells (line l) old π))
      (stagePermutationMeasure P B) t * doubleBlockSignedSwapBound cells (line l) lo hi t positive
  have hbound (l : Fin m) (positive : Bool) : moment l positive ≤
      Real.exp ((V / 4) * t ^ 2 / 2) := by
    calc
      _ ≤ Real.exp (doubleBlockCombinedProxy cells (line l) lo hi * t ^ 2 / 2) :=
        double_block_signed_moment_le_proxy cells (line l) old lo hi hinterval t positive
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (sub_nonneg.mpr (hinvoice l)) (sq_nonneg t)]
  have hlog := mixed_moment_log_failure_budget hm V hV moment (by simpa [t, E] using hbound)
  obtain ⟨ht, _, hbudget⟩ := hlog
  have h := double_block_simultaneous_sample_exists hB cells line old lo hi
    (fun _ => E) (fun _ => t) (fun _ => by simpa [t, E] using ht) hinterval (by
      simpa [moment, t, E] using hbudget)
  simpa [E] using h


end
end Sude
