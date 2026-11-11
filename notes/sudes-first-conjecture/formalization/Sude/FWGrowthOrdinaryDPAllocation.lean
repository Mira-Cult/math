import Sude.PrefixDeterministicFourWeight
import Sude.FWGrowthDiagonalSlots
import Sude.FWGrowthNarrowPD2

/-! Simultaneous deterministic allocation for the actual indexed ordinary
labels of a narrowed growth trace. Physical realization is separate. -/
namespace Sude
noncomputable section

/-- The stage-tagged ordinary slots, with stage occurrences kept distinct. -/
def fwGrowthOrdinaryPopulation (n P : ℕ) : Finset (Fin P × Fin (6 * (n+8))) :=
  Finset.univ.product (fwGrowthOrdinarySlots n)

/-- Narrowed stagewise growth midpoints admit one simultaneous stage-preserving
assignment of the existing ordinary labels. The midpoint labels are precisely
those present after an arbitrary prior stage permutation `ω₀`; the corresponding
rectangle labels are outside this population. Supplied line weights have global
column mass at most four. The stage means here are the means of the ordinary
labels, not the original full-stage means. This does not realize the assignment
on physical cells. -/
theorem fw_growth_ordinary_dp_assignment {n : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial radius final last stages)
    (X : ℝ) (hX : 0 ≤ X) (hnarrow : NarrowedStages (X/6) stages)
    (ω₀ : Fin stages.length → Equiv.Perm (Fin (6*(n+8))))
    {L : Type*} [DecidableEq L] (lines : Finset L)
    (w : L → (Fin stages.length × Fin (6*(n+8))) → ℝ)
    (hw : ∀ l ∈ lines, ∀ s ∈ fwGrowthOrdinaryPopulation n stages.length, 0 ≤ w l s)
    (hweight : ∀ s ∈ fwGrowthOrdinaryPopulation n stages.length, (∑ l ∈ lines, w l s) ≤ 4) :
    let population := fwGrowthOrdinaryPopulation n stages.length
    let midpoint := fun s : Fin stages.length × Fin (6*(n+8)) =>
      growthStageMidpoint (stages.get s.1) (trace.lowAt rfl s.1 (ω₀ s.1 s.2))
    ∃ e : {s // s ∈ population} ≃ {s // s ∈ population},
      (∀ s, (e s).val.1 = s.val.1) ∧
      (∀ l ∈ lines,
        |(∑ s : {s // s ∈ population}, w l s.val * midpoint (e s).val) -
          ∑ j ∈ population.image Prod.fst,
            (∑ s ∈ population.filter (fun s => s.1 = j), w l s) *
              prefixOriginalStageMean population Prod.fst midpoint j| ≤
          (Nat.clog 2 (6*n) : ℝ) * (8 * (X/6))) := by
  classical
  dsimp only
  let population := fwGrowthOrdinaryPopulation n stages.length
  let midpoint : (Fin stages.length × Fin (6*(n+8))) → ℝ := fun s =>
    growthStageMidpoint (stages.get s.1) (trace.lowAt rfl s.1 (ω₀ s.1 s.2))
  have hcap : ∀ j, (population.filter (fun s => s.1 = j)).card ≤ 6*n := by
    intro j
    have heq : population.filter (fun s => s.1 = j) =
        ({j} : Finset (Fin stages.length)).product (fwGrowthOrdinarySlots n) := by
      ext ⟨k,i⟩
      simp [population, fwGrowthOrdinaryPopulation, eq_comm, and_comm]
    rw [heq]
    change (({j} : Finset (Fin stages.length)) ×ˢ fwGrowthOrdinarySlots n).card ≤ 6*n
    rw [Finset.card_product, Finset.card_singleton, one_mul]
    exact le_of_eq (fw_growth_slot_group_cardinalities n).2.2.2
  have hwidth : ∀ u ∈ population, ∀ v ∈ population,
      Prod.fst u = Prod.fst v → midpoint v - midpoint u ≤ X/6 := by
    rintro ⟨j,i⟩ _ ⟨k,t⟩ _ hstage
    dsimp only [Prod.fst] at hstage
    subst k
    have hu := trace.lowAt_mem rfl j (ω₀ j i)
    have hv := trace.lowAt_mem rfl j (ω₀ j t)
    have h := hnarrow (stages.get j) (List.get_mem _ _) _ (by simpa [BTStageTrace.stageAt] using hv)
      _ (by simpa [BTStageTrace.stageAt] using hu)
    exact le_of_lt (abs_lt.mp h).2
  exact prefix_deterministic_stage_assignment_four population population lines Prod.fst Prod.fst midpoint w
    (X/6) (6*n) (div_nonneg hX (by norm_num)) (fun _ => rfl) hcap hw hweight hwidth

end
end Sude
