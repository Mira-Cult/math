import Sude.PrefixWeightedCenteredBound
import Sude.PrefixPopulationMeanWidth

/-! A finite pair-slot family centered at actual labelled-stage means. -/
namespace Sude
noncomputable section

/-- Each slot uses an actual member of its own stage population. If stage
value widths are at most `C` and nonnegative slot weights total at most two,
the entire weighted deviation from original stage means is at most `2*C`.
No geometry, stage assignment, or line-incidence facts are inferred. -/
theorem prefix_weighted_population_deviation {I G A : Type*}
    (slots : Finset I) (stage : I → G) (pop : G → Finset A)
    (value : G → A → ℝ) (label : I → A) (weight : I → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hw : ∀ i ∈ slots, 0 ≤ weight i)
    (hmass : (∑ i ∈ slots, weight i) ≤ 2)
    (hlabel : ∀ i ∈ slots, label i ∈ pop (stage i))
    (hwidth : ∀ g, ∀ a ∈ pop g, ∀ b ∈ pop g, value g b - value g a ≤ C) :
    |∑ i ∈ slots, weight i *
      (value (stage i) (label i) -
        (∑ a ∈ pop (stage i), value (stage i) a) / (pop (stage i)).card)| ≤ 2 * C := by
  apply prefix_weighted_centered_bound slots weight _ C hC hw hmass
  intro i hi
  exact prefix_population_member_mean_width (pop (stage i)) (value (stage i)) C
    (hwidth (stage i)) (label i) (hlabel i hi)

end
end Sude
