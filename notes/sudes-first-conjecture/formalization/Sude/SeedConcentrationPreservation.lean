import Sude.PhysicalPairLineSum

/-! A pointwise-preserved finite seed-cell image retains its physical
line concentration with the original midpoint reference. -/
namespace Sude
noncomputable section

/-- A finite selected-cell sum is unchanged by pointwise preservation on
the cell map. The map need not be injective. -/
theorem selected_cell_line_sum_preserved {α : Type*} [Fintype α] {n : ℕ}
    (cells : α → Cell n) (line : Cell n → Prop) [DecidablePred line]
    (old new : Cell n ≃ Fin (n * n))
    (hfixed : ∀ x, entry new (cells x) = entry old (cells x)) :
    (∑ c ∈ (Finset.univ.image cells).filter line, (entry new c : ℝ)) =
      ∑ c ∈ (Finset.univ.image cells).filter line, (entry old c : ℝ) := by
  classical
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hc).1
  rw [hfixed x]

/-- Every labelled selected-seed bound is preserved with exactly the same
source-stage midpoint reference and physical orientation term. -/
theorem seed_selected_line_concentration_preserved {ι Λ : Type*} [Fintype ι] {n : ℕ}
    (cells : ι × Bool → Cell n) (line : Λ → Cell n → Prop)
    [∀ l, DecidablePred (line l)]
    (old new : Cell n ≃ Fin (n * n)) (reference : Λ → ℝ) (B : ℝ)
    (hfixed : ∀ x, entry new (cells x) = entry old (cells x))
    (hselected : ∀ l, |(∑ c ∈ (Finset.univ.image cells).filter (line l), (entry old c : ℝ)) -
      reference l - (∑ p, physicalPairLineOrientation cells (line l) p * ((2 : ℝ) / 2))| ≤ B) :
    ∀ l, |(∑ c ∈ (Finset.univ.image cells).filter (line l), (entry new c : ℝ)) -
      reference l - (∑ p, physicalPairLineOrientation cells (line l) p * ((2 : ℝ) / 2))| ≤ B := by
  intro l
  rw [selected_cell_line_sum_preserved cells (line l) old new hfixed]
  exact hselected l


/-- The source-stage reference used by the selected seed line estimate.
It is defined from `grown`, and is unchanged by later modifications to the
other square. -/
def seedSourceMidpointReference {n P Q : ℕ} {Λ : Type*}
    (cells : (Fin P × Fin Q) × Bool → Cell n) (line : Λ → Cell n → Prop)
    (grown : Cell n ≃ Fin (n * n)) (l : Λ) : ℝ :=
  ∑ j, (∑ q, physicalPairLineWeight cells (line l) (j,q)) *
    ((∑ q, (((entry grown (cells ((j,q),false)) : ℝ) +
      entry grown (cells ((j,q),true))) / 2)) / (Q : ℝ))

/-- Pointwise preservation of every seed slot transfers the selected-seed
physical concentration, retaining the same grown-square midpoint reference
and the same oriented gap-two contribution. No seed-cell injection is needed. -/
theorem seed_source_midpoint_concentration_preserved {n P Q : ℕ} {Λ : Type*}
    (cells : (Fin P × Fin Q) × Bool → Cell n) (line : Λ → Cell n → Prop)
    [∀ l, DecidablePred (line l)] (grown before after : Cell n ≃ Fin (n * n)) (B : ℝ)
    (hfixed : ∀ x, entry after (cells x) = entry before (cells x))
    (hselected : ∀ l, |(∑ c ∈ (Finset.univ.image cells).filter (line l), (entry before c : ℝ)) -
      seedSourceMidpointReference cells line grown l -
      (∑ p, physicalPairLineOrientation cells (line l) p * ((2 : ℝ) / 2))| ≤ B) :
    ∀ l, |(∑ c ∈ (Finset.univ.image cells).filter (line l), (entry after c : ℝ)) -
      seedSourceMidpointReference cells line grown l -
      (∑ p, physicalPairLineOrientation cells (line l) p * ((2 : ℝ) / 2))| ≤ B := by
  exact seed_selected_line_concentration_preserved cells line before after
    (seedSourceMidpointReference cells line grown) B hfixed hselected

/-- A previously established stage-wise seed permutation equation transfers
along the same pointwise seed-cell preservation. -/
theorem seed_pair_permutation_preserved {n P Q : ℕ}
    (cells : (Fin P × Fin Q) × Bool → Cell n)
    (grown before after : Cell n ≃ Fin (n * n)) (ω : Fin P → Equiv.Perm (Fin Q))
    (hfixed : ∀ x, entry after (cells x) = entry before (cells x))
    (hperm : ∀ j q side, entry before (cells ((j,q),side)) = entry grown (cells ((j,ω j q),side))) :
    ∀ j q side, entry after (cells ((j,q),side)) = entry grown (cells ((j,ω j q),side)) := by
  intro j q side
  rw [hfixed, hperm]

end
end Sude
