import Sude.PrefixRoundingJointStep

/-! Extension of one joint fractional-coordinate step to a finite ambient
population. Termination, dropped-line errors and recursive allocation remain
separate. -/
namespace Sude
noncomputable section

/-- Extend one joint DP2 step by freezing all nonfractional coordinates.
The resulting fractional set is strictly smaller; all full group and retained
line sums over the supplied ambient population are preserved. -/
theorem prefix_rounding_freeze_step {S G L : Type*} [DecidableEq S] [DecidableEq G]
    (U F : Finset S) (group : S → G) (R : Finset L) (x : S → ℝ)
    (a : L → S → ℝ) (C : ℝ) (hC : 0 ≤ C) (hF : F.Nonempty)
    (hFexact : F = U.filter (fun s => 0 < x s ∧ x s < 1))
    (hbox : ∀ s ∈ U, 0 ≤ x s ∧ x s ≤ 1)
    (hint : ∀ g ∈ F.image group, ∃ z : ℤ,
      (∑ s ∈ F.filter (fun s => group s = g), x s) = z)
    (hnonneg : ∀ l ∈ R, ∀ s ∈ F, 0 ≤ a l s)
    (hrow : ∀ l ∈ R, 10 * C < ∑ s ∈ F, a l s)
    (hcol : ∀ s ∈ F, (∑ l ∈ R, a l s) ≤ 5 * C) :
    ∃ z : S → ℝ,
      (∀ s ∈ U, 0 ≤ z s ∧ z s ≤ 1) ∧
      (∀ s, s ∉ F → z s = x s) ∧
      (U.filter (fun s => 0 < z s ∧ z s < 1)).card < F.card ∧
      (∀ g, (∑ s ∈ U, if group s = g then z s else 0) =
        ∑ s ∈ U, if group s = g then x s else 0) ∧
      (∀ l ∈ R, (∑ s ∈ U, a l s * z s) = ∑ s ∈ U, a l s * x s) := by
  classical
  have hFU : F ⊆ U := by rw [hFexact]; exact Finset.filter_subset _ _
  have hx : ∀ s ∈ F, 0 < x s ∧ x s < 1 := by
    intro s hs
    rw [hFexact] at hs
    exact (Finset.mem_filter.mp hs).2
  obtain ⟨y, hybox, hyboundary, hygroup, hyline⟩ :=
    prefix_joint_rounding_step F group R x a C hC hF hx hint hnonneg hrow hcol
  let z : S → ℝ := fun s => if hs : s ∈ F then y ⟨s, hs⟩ else x s
  have hzF (s : {s // s ∈ F}) : z s.val = y s := by simp [z, s.property]
  have hzout : ∀ s, s ∉ F → z s = x s := by intro s hs; simp [z, hs]
  have hactivegroup (g : G) :
      (∑ s ∈ F, if group s = g then z s else 0) =
        ∑ s ∈ F, if group s = g then x s else 0 := by
    rw [Finset.sum_subtype F (fun _ => Iff.rfl), Finset.sum_subtype F (fun _ => Iff.rfl)]
    by_cases hg : g ∈ F.image group
    · simpa only [hzF] using hygroup ⟨g, hg⟩
    · have hnone : ∀ s : {s // s ∈ F}, group s.val ≠ g := by
        intro s heq
        apply hg
        exact Finset.mem_image.mpr ⟨s.val, s.property, heq⟩
      simp [hnone]
  have hactiveline (l : L) (hl : l ∈ R) :
      (∑ s ∈ F, a l s * z s) = ∑ s ∈ F, a l s * x s := by
    rw [Finset.sum_subtype F (fun _ => Iff.rfl), Finset.sum_subtype F (fun _ => Iff.rfl)]
    simpa only [hzF] using hyline ⟨l, hl⟩
  refine ⟨z, ?_, hzout, ?_, ?_, ?_⟩
  · intro s hs
    by_cases hsF : s ∈ F
    · simpa [z, hsF] using hybox ⟨s, hsF⟩
    · simpa [hzout s hsF] using hbox s hs
  · let F' := U.filter (fun s => 0 < z s ∧ z s < 1)
    have hsub : F' ⊆ F := by
      intro s hs
      obtain ⟨hsU, hsZ⟩ := Finset.mem_filter.mp hs
      by_contra hn
      have he := hzout s hn
      have hsF : s ∈ F := by rw [hFexact]; exact Finset.mem_filter.mpr ⟨hsU, by simpa [he] using hsZ⟩
      exact hn hsF
    obtain ⟨s, hs0 | hs1⟩ := hyboundary
    · have hsnot : s.val ∉ F' := by
        intro hs
        have hpos := (Finset.mem_filter.mp hs).2.1
        rw [hzF s, hs0] at hpos
        linarith
      have hss : F' ⊂ F := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
        intro heq
        exact hsnot ((congrArg (fun q : Finset S => s.val ∈ q) heq).mpr s.property)⟩
      exact Finset.card_lt_card hss
    · have hsnot : s.val ∉ F' := by
        intro hs
        have hlt := (Finset.mem_filter.mp hs).2.2
        rw [hzF s, hs1] at hlt
        linarith
      have hss : F' ⊂ F := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
        intro heq
        exact hsnot ((congrArg (fun q : Finset S => s.val ∈ q) heq).mpr s.property)⟩
      exact Finset.card_lt_card hss
  · intro g
    have hout : (∑ s ∈ U \ F, if group s = g then z s else 0) =
        ∑ s ∈ U \ F, if group s = g then x s else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hzout s (Finset.mem_sdiff.mp hs).2]
    have h1 := Finset.sum_sdiff (f := fun s => if group s = g then z s else 0) hFU
    have h2 := Finset.sum_sdiff (f := fun s => if group s = g then x s else 0) hFU
    rw [← h1, ← h2, hout, hactivegroup g]
  · intro l hl
    have hout : (∑ s ∈ U \ F, a l s * z s) = ∑ s ∈ U \ F, a l s * x s := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hzout s (Finset.mem_sdiff.mp hs).2]
    have h1 := Finset.sum_sdiff (f := fun s => a l s * z s) hFU
    have h2 := Finset.sum_sdiff (f := fun s => a l s * x s) hFU
    rw [← h1, ← h2, hout, hactiveline l hl]

end
end Sude
