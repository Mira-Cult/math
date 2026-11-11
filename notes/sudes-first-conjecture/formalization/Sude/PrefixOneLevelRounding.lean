import Sude.PrefixRoundingFreezeStep
import Sude.PrefixFractionalGroupIntegral
import Sude.PrefixRoundingDropError

/-! One finite simultaneous rounding level. This proves no recursive
assignment of stage values to slots. -/
namespace Sude
noncomputable section

/-- Rounding a finite unit-box vector to zero/one preserves every integral
initial group sum. All line errors are bounded simultaneously by `10*C`.
The coefficient column bound is global across all lines and the line error is
charged once at the time of dropping, not once per intermediate step. -/
theorem prefix_one_level_rounding {S G L : Type*} [DecidableEq S] [DecidableEq G] [DecidableEq L]
    (U : Finset S) (group : S → G) (lines : Finset L) (a : L → S → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (ha : ∀ l ∈ lines, ∀ s ∈ U, 0 ≤ a l s)
    (hcol : ∀ s ∈ U, (∑ l ∈ lines, a l s) ≤ 5 * C)
    (x : S → ℝ) (hbox : ∀ s ∈ U, 0 ≤ x s ∧ x s ≤ 1)
    (hint : ∀ g, ∃ z : ℤ, (∑ s ∈ U, if group s = g then x s else 0) = z) :
    ∃ y : S → ℝ,
      (∀ s ∈ U, y s = 0 ∨ y s = 1) ∧
      (∀ s, s ∉ U.filter (fun s => 0 < x s ∧ x s < 1) → y s = x s) ∧
      (∀ g, (∑ s ∈ U, if group s = g then y s else 0) =
        ∑ s ∈ U, if group s = g then x s else 0) ∧
      (∀ l ∈ lines, |∑ s ∈ U, a l s * (y s - x s)| ≤ 10 * C) := by
  classical
  have main : ∀ k : ℕ, ∀ (x : S → ℝ) (R : Finset L),
      (U.filter (fun s => 0 < x s ∧ x s < 1)).card = k →
      R ⊆ lines →
      (∀ s ∈ U, 0 ≤ x s ∧ x s ≤ 1) →
      (∀ g, ∃ z : ℤ, (∑ s ∈ U, if group s = g then x s else 0) = z) →
      ∃ y : S → ℝ,
        (∀ s ∈ U, y s = 0 ∨ y s = 1) ∧
        (∀ s, s ∉ U.filter (fun s => 0 < x s ∧ x s < 1) → y s = x s) ∧
        (∀ g, (∑ s ∈ U, if group s = g then y s else 0) =
          ∑ s ∈ U, if group s = g then x s else 0) ∧
        (∀ l ∈ R, |∑ s ∈ U, a l s * (y s - x s)| ≤ 10 * C) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x R hk hRL hbox hint
      let F := U.filter (fun s => 0 < x s ∧ x s < 1)
      have hFU : F ⊆ U := Finset.filter_subset _ _
      by_cases hF : F.Nonempty
      · let R' := R.filter (fun l => 10 * C < ∑ s ∈ F, a l s)
        have hR'R : R' ⊆ R := Finset.filter_subset _ _
        have hR'L : R' ⊆ lines := hR'R.trans hRL
        have hfracint : ∀ g ∈ F.image group, ∃ z : ℤ,
            (∑ s ∈ F.filter (fun s => group s = g), x s) = z := by
          intro g hg
          have hfilter : (U.filter (fun s => group s = g)).filter
              (fun s => 0 < x s ∧ x s < 1) = F.filter (fun s => group s = g) := by
            ext s
            simp [F, and_comm, and_assoc]
          have hfull : ∃ z : ℤ, (∑ s ∈ U.filter (fun s => group s = g), x s) = z := by
            simpa [Finset.sum_filter] using hint g
          have hres := prefix_fractional_group_sum_integral
            (U.filter (fun s => group s = g)) x
            (fun s hs => hbox s (Finset.mem_filter.mp hs).1) hfull
          simpa [hfilter] using hres
        have hnonneg : ∀ l ∈ R', ∀ s ∈ F, 0 ≤ a l s := by
          intro l hl s hs
          exact ha l (hR'L hl) s (hFU hs)
        have hrow : ∀ l ∈ R', 10 * C < ∑ s ∈ F, a l s := by
          intro l hl
          exact (Finset.mem_filter.mp hl).2
        have hcol' : ∀ s ∈ F, (∑ l ∈ R', a l s) ≤ 5 * C := by
          intro s hs
          have hsU := hFU hs
          have hsub : (∑ l ∈ R', a l s) ≤ ∑ l ∈ lines, a l s := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hR'L
            intro l hl _
            exact ha l hl s hsU
          exact hsub.trans (hcol s hsU)
        obtain ⟨z, hzbox, hzfreeze, hzsmall, hzgroup, hzline⟩ :=
          prefix_rounding_freeze_step U F group R' x a C hC hF rfl hbox hfracint hnonneg hrow hcol'
        let Fz := U.filter (fun s => 0 < z s ∧ z s < 1)
        have hFzF : Fz ⊆ F := by
          intro s hs
          obtain ⟨hsU, hzfrac⟩ := Finset.mem_filter.mp hs
          by_contra hnot
          have he := hzfreeze s hnot
          have : s ∈ F := Finset.mem_filter.mpr ⟨hsU, by simpa [he] using hzfrac⟩
          exact hnot this
        have hzint : ∀ g, ∃ v : ℤ,
            (∑ s ∈ U, if group s = g then z s else 0) = v := by
          intro g
          obtain ⟨v, hv⟩ := hint g
          exact ⟨v, (hzgroup g).trans hv⟩
        have hlt : Fz.card < k := by simpa [Fz, F, hk] using hzsmall
        obtain ⟨y, hybinary, hyfreeze, hygroup, hyline⟩ :=
          ih Fz.card hlt z R' rfl hR'L hzbox hzint
        have hyfreezeF : ∀ s, s ∉ F → y s = x s := by
          intro s hs
          have hs' : s ∉ Fz := fun hm => hs (hFzF hm)
          exact (hyfreeze s hs').trans (hzfreeze s hs)
        have hybox : ∀ s ∈ U, 0 ≤ y s ∧ y s ≤ 1 := by
          intro s hs
          rcases hybinary s hs with h0 | h1
          · simp [h0]
          · simp [h1]
        refine ⟨y, hybinary, hyfreezeF, ?_, ?_⟩
        · intro g
          exact (hygroup g).trans (hzgroup g)
        · intro l hl
          by_cases hl' : l ∈ R'
          · have heq : (∑ s ∈ U, a l s * (y s - x s)) =
                ∑ s ∈ U, a l s * (y s - z s) := by
              simp only [mul_sub, Finset.sum_sub_distrib]
              rw [hzline l hl']
            rw [heq]
            exact hyline l hl'
          · have hmass : (∑ s ∈ F, a l s) ≤ 10 * C := by
              have hn : ¬ 10 * C < ∑ s ∈ F, a l s := by
                intro hm
                exact hl' (Finset.mem_filter.mpr ⟨hl, hm⟩)
              exact le_of_not_gt hn
            exact prefix_rounding_drop_error_bound U F (a l) x y C hFU
              (fun s hs => ha l (hRL hl) s (hFU hs))
              (fun s hs => hbox s (hFU hs))
              (fun s hs => hybox s (hFU hs))
              (fun s _ hs => hyfreezeF s hs) hmass
      · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
        refine ⟨x, ?_, ?_, ?_, ?_⟩
        · intro s hs
          have hn : ¬(0 < x s ∧ x s < 1) := by
            intro hh
            have : s ∈ F := Finset.mem_filter.mpr ⟨hs, hh⟩
            simp [hFempty] at this
          obtain ⟨h0, h1⟩ := hbox s hs
          by_cases hzero : x s = 0
          · exact Or.inl hzero
          · right
            by_contra hnot
            have hp : 0 < x s := lt_of_le_of_ne h0 (Ne.symm hzero)
            have hlt : x s < 1 := lt_of_le_of_ne h1 hnot
            exact hn ⟨hp, hlt⟩
        · intro s hs; rfl
        · intro g; rfl
        · intro l hl
          simpa using mul_nonneg (show (0 : ℝ) ≤ 10 by norm_num) hC
  exact main (U.filter (fun s => 0 < x s ∧ x s < 1)).card x lines rfl (Finset.Subset.rfl) hbox hint

end
end Sude
