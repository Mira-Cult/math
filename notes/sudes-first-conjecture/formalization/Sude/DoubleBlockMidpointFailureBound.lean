import Sude.DoubleBlockLogSelection
import Sude.StageSwapFailureBound

/-! The logarithmic midpoint invoice bounds the bad event on the same joint
stage-permutation and swap product used for later simultaneous selection.
No physical placement or previously chosen witness is asserted. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory

local instance doubleBlockFailurePermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- The existing midpoint invoice gives failure probability at most one half,
on the actual joint uniform stage-permutation and fair-swap space. -/
theorem double_block_log_midpoint_failure_bound {n P B m : ℕ}
    (hB : 0 < B) (hm : 0 < m) (V : ℝ) (hV : 0 < V)
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Fin m → Cell n → Prop) (old : Cell n ≃ Fin (n * n)) (lo hi : Fin P → ℝ)
    (hinterval : ∀ j b p, doubleBlockPairMidpoint cells old j b p ∈ Set.Icc (lo j) (hi j))
    (hinvoice : ∀ l, doubleBlockCombinedProxy cells (line l) lo hi ≤ V / 4) :
    let E := Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2)
    ((stagePermutationMeasure P B).prod
      (uniformOn (Set.univ : Set ((Fin P × Fin B) → Bool)))).real
      {z | ∃ l, E ≤ |doubleBlockSampleScore cells (line l) old z.1 z.2|} ≤ (1/2 : ℝ) := by
  classical
  dsimp only
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
  obtain ⟨ht, hbudget, _⟩ := hlog
  have hmoment (l : Fin m) (positive : Bool) :
      (∑ π, ∑ s : (Fin P × Fin B) → Bool,
        Real.exp (t * (if positive then doubleBlockSampleScore cells (line l) old π s
          else -doubleBlockSampleScore cells (line l) old π s))) /
        ((Fintype.card (Fin P → Equiv.Perm (Fin B)) : ℝ) *
          (2 : ℝ) ^ Fintype.card (Fin P × Fin B)) ≤ moment l positive := by
    have h := stage_fair_swap_exp_moment (ι := Fin P × Fin B) P B
      (fun π => doubleBlockSign positive (doubleBlockStageScore cells (line l) old π))
      (fun π i => doubleBlockPairMidpoint cells old i.1 (π i.1 i.2) 0)
      (fun π i => doubleBlockPairMidpoint cells old i.1 (π i.1 i.2) 1)
      (fun i => doubleBlockSign positive (physicalPairLineWeight cells (line l) (i.1,i.2,0)))
      (fun i => doubleBlockSign positive (physicalPairLineWeight cells (line l) (i.1,i.2,1)))
      (fun i => lo i.1) (fun i => hi i.1) t
      (by intro π i; exact hinterval i.1 (π i.1 i.2) 0)
      (by intro π i; exact hinterval i.1 (π i.1 i.2) 1)
    have hscore (π : Fin P → Equiv.Perm (Fin B)) (s : (Fin P × Fin B) → Bool) :
      (if positive then doubleBlockSampleScore cells (line l) old π s else
        -doubleBlockSampleScore cells (line l) old π s) =
      doubleBlockSign positive (doubleBlockStageScore cells (line l) old π) + ∑ i : Fin P × Fin B,
        (fairBlockSwapValue (doubleBlockPairMidpoint cells old i.1 (π i.1 i.2) 0)
          (doubleBlockPairMidpoint cells old i.1 (π i.1 i.2) 1)
          (doubleBlockSign positive (physicalPairLineWeight cells (line l) (i.1,i.2,0)))
          (doubleBlockSign positive (physicalPairLineWeight cells (line l) (i.1,i.2,1))) (s i) -
        (doubleBlockSign positive (physicalPairLineWeight cells (line l) (i.1,i.2,0)) +
          doubleBlockSign positive (physicalPairLineWeight cells (line l) (i.1,i.2,1))) *
          (doubleBlockPairMidpoint cells old i.1 (π i.1 i.2) 0 +
            doubleBlockPairMidpoint cells old i.1 (π i.1 i.2) 1) / 2) := by
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
    simpa only [hscore, moment, doubleBlockSignedSwapBound] using h
  have hfail := stage_swap_failure_bound P B
    (fun l π s => doubleBlockSampleScore cells (line l) old π s)
    (fun _ => E) (fun _ => t) moment (fun _ => by simpa [t,E] using ht) hmoment
  exact hfail.trans (by simpa [moment,t,E] using hbudget)

end
end Sude
