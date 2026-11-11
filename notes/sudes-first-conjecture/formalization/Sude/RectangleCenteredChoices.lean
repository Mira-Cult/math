import Sude.FamilyGrid

/-! Independently centered subset choices for the main and anti families
of packed rectangle labels. This is a subset-sum interface; it does not
construct rectangle trades or prime targets. -/
namespace Sude
noncomputable section

/-- One selected reference subset centers both disjoint rectangle families.
For any two independently supplied bounded even signed differences, one later
subset realizes both differences relative to that same reference. The two
complete grids and the orientation choice are explicit inputs. -/
theorem rectangle_centered_choices {L : ℕ} (S : Finset (Fin L))
    (choice : Fin L → Bool) (gap : Fin L → ℕ) (Rm Ra : ℕ)
    (hm : CompleteEvenGrid (S.filter fun i => choice i = true) gap Rm)
    (ha : CompleteEvenGrid (S.filter fun i => choice i = false) gap Ra) :
    ∃ before : Finset (Fin L), before ⊆ S ∧
      ((∑ i ∈ before ∩ (S.filter fun i => choice i = true), gap i : ℕ) : ℤ) = evenGridCenter Rm ∧
      ((∑ i ∈ before ∩ (S.filter fun i => choice i = false), gap i : ℕ) : ℤ) = evenGridCenter Ra ∧
      ∀ tm ta : ℤ, (2 : ℤ) ∣ tm → (2 : ℤ) ∣ ta →
        -(evenGridCenter Rm : ℤ) ≤ tm → tm ≤ evenGridCenter Rm →
        -(evenGridCenter Ra : ℤ) ≤ ta → ta ≤ evenGridCenter Ra →
        ∃ after : Finset (Fin L), after ⊆ S ∧
          ((∑ i ∈ after ∩ (S.filter fun i => choice i = true), gap i : ℕ) : ℤ) -
            ((∑ i ∈ before ∩ (S.filter fun i => choice i = true), gap i : ℕ) : ℤ) = tm ∧
          ((∑ i ∈ after ∩ (S.filter fun i => choice i = false), gap i : ℕ) : ℤ) -
            ((∑ i ∈ before ∩ (S.filter fun i => choice i = false), gap i : ℕ) : ℤ) = ta := by
  classical
  let block : Bool → Finset (Fin L) := fun b => S.filter fun i => choice i = b
  let radius : Bool → ℕ := fun b => if b then Rm else Ra
  have hdisj : ∀ e f, e ≠ f → Disjoint (block e) (block f) := by
    intro e f hne
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have he : choice i = e := (Finset.mem_filter.mp hi).2
    have hf : choice i = f := (Finset.mem_filter.mp hj).2
    exact hne (he.symm.trans hf)
  have hgrids : ∀ e, CompleteEvenGrid (block e) gap (radius e) := by
    intro e
    cases e <;> simp [block, radius, hm, ha]
  have hunion : Finset.univ.biUnion block = S := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, block, Finset.mem_filter]
    constructor
    · rintro ⟨e, hi, _⟩
      exact hi
    · intro hi
      exact ⟨choice i, hi, rfl⟩
  obtain ⟨before, hbefore, hcenter, hchoose⟩ :=
    simultaneous_centered_subsets block gap radius hdisj hgrids
  refine ⟨before, by simpa only [hunion] using hbefore, ?_, ?_, ?_⟩
  · simpa [block, radius] using hcenter true
  · simpa [block, radius] using hcenter false
  · intro tm ta htm hta hml hmu hal hau
    let t : Bool → ℤ := fun b => if b then tm else ta
    have heven : ∀ e, (2 : ℤ) ∣ t e := by
      intro e
      cases e <;> simp [t, htm, hta]
    have hlow : ∀ e, -(evenGridCenter (radius e) : ℤ) ≤ t e := by
      intro e
      cases e <;> simp [t, radius, hml, hal]
    have hhigh : ∀ e, t e ≤ evenGridCenter (radius e) := by
      intro e
      cases e <;> simp [t, radius, hmu, hau]
    obtain ⟨after, hafter, hsum⟩ := hchoose t heven hlow hhigh
    refine ⟨after, by simpa only [hunion] using hafter, ?_, ?_⟩
    · simpa [block, radius, t] using hsum true
    · simpa [block, radius, t] using hsum false

end
end Sude
