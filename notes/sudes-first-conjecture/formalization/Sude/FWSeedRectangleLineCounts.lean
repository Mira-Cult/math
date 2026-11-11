import Sude.FWSeedLineIncidence

/-! Unsquared incidence of the actual complete seed rectangles.
No diagonal or completed-line bound is asserted. -/
namespace Sude
noncomputable section

private theorem paired_indicator_sum {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f g : α → β) (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ i k, f i ≠ g k) (r : β) :
    (∑ i, ((if f i = r then (2:ℝ) else 0) + (if g i = r then (2:ℝ) else 0))) =
      if ∃ i, f i = r ∨ g i = r then 2 else 0 := by
  classical
  have unique : ∀ i k, (f i = r ∨ g i = r) → (f k = r ∨ g k = r) → i = k := by
    intro i k hi hk
    rcases hi with hi | hi <;> rcases hk with hk | hk
    · exact hf (hi.trans hk.symm)
    · exact False.elim (hfg i k (hi.trans hk.symm))
    · exact False.elim (hfg k i (hk.trans hi.symm))
    · exact hg (hi.trans hk.symm)
  by_cases he : ∃ i, f i = r ∨ g i = r
  · obtain ⟨i, hi⟩ := he
    have hsumi : (∑ k, ((if f k = r then (2:ℝ) else 0) + (if g k = r then (2:ℝ) else 0))) = 2 := by
      calc
        _ = ((if f i = r then (2:ℝ) else 0) + (if g i = r then (2:ℝ) else 0)) := by
          apply Finset.sum_eq_single i
          · intro k _ hki
            have hn : ¬ (f k = r ∨ g k = r) := by
              intro hk
              exact hki (unique k i hk hi)
            push Not at hn
            simp [hn.1, hn.2]
          · simp
        _ = 2 := by
          rcases hi with h1 | h2
          · have h2n : g i ≠ r := by
              intro h2
              exact hfg i i (h1.trans h2.symm)
            simp [h1, h2n]
          · have h1n : f i ≠ r := by
              intro h1
              exact hfg i i (h1.trans h2.symm)
            simp [h1n, h2]
    simp only [if_pos (show ∃ i, f i = r ∨ g i = r from ⟨i, hi⟩)]
    exact hsumi
  · have hn : ∀ i, f i ≠ r ∧ g i ≠ r := by simpa using he
    simp only [if_neg he]
    apply Finset.sum_eq_zero
    intro i _
    simp [(hn i).1, (hn i).2]

private theorem rectangle_row_pair_sum {n L : ℕ} (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (i : Fin L) (r : Fin n) :
    (∑ p : Fin 2, rectanglePairWeight hs choice (fun c => c.1 = r) (i,p)) =
      (if RectanglePacking.firstRow hs i = r then (2:ℝ) else 0) +
      (if RectanglePacking.secondRow hs i = r then (2:ℝ) else 0) := by
  classical
  simp [Fin.sum_univ_two, rectanglePairWeight, prefixPairCorner, packedRectangleCorner]
  split_ifs <;> norm_num

private theorem rectangle_column_pair_sum {n L : ℕ} (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (i : Fin L) (c : Fin n) :
    (∑ p : Fin 2, rectanglePairWeight hs choice (fun x => x.2 = c) (i,p)) =
      (if RectanglePacking.firstColumn hs choice i = c then (2:ℝ) else 0) +
      (if RectanglePacking.secondColumn hs choice i = c then (2:ℝ) else 0) := by
  classical
  simp [Fin.sum_univ_two, rectanglePairWeight, prefixPairCorner, packedRectangleCorner]
  split_ifs <;> norm_num

private theorem seed_stage_index_injective {L : ℕ}
    (hseed : 5*(4*6)+16*(4*6) ≤ L) (j : Fin 16) :
    Function.Injective (fun i : Fin (4*6) => fwSeedRectangle hseed (finProdFinEquiv (j,i))) := by
  intro i k h
  exact congrArg Prod.snd (finProdFinEquiv.injective (fwSeedRectangle_injective hseed h))

/-- The extra stage rectangle incidence is exactly zero or two. -/
theorem fw_seed_rectangle_row_stage_weight {n L : ℕ}
    (hseed : 5*(4*6)+16*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (j : Fin 16) (r : Fin n) :
    fwSeedRectangleStageLineWeight hseed hs choice (fun c => c.1 = r) j =
      if ∃ i : Fin (4*6),
        RectanglePacking.firstRow hs (fwSeedRectangle hseed (finProdFinEquiv (j,i))) = r ∨
        RectanglePacking.secondRow hs (fwSeedRectangle hseed (finProdFinEquiv (j,i))) = r
      then 2 else 0 := by
  classical
  let idx := fun i : Fin (4*6) => fwSeedRectangle hseed (finProdFinEquiv (j,i))
  have hi : Function.Injective idx := seed_stage_index_injective hseed j
  unfold fwSeedRectangleStageLineWeight
  simp_rw [rectangle_row_pair_sum]
  have h := paired_indicator_sum (fun i => RectanglePacking.firstRow hs (idx i))
    (fun i => RectanglePacking.secondRow hs (idx i))
    ((RectanglePacking.firstRow_injective hs).comp hi)
    ((RectanglePacking.secondRow_injective hs).comp hi)
    (fun i k => RectanglePacking.firstRow_ne_secondRow hs (idx i) (idx k)) r
  by_cases hex : ∃ i, RectanglePacking.firstRow hs (idx i) = r ∨ RectanglePacking.secondRow hs (idx i) = r
  · dsimp only [idx] at h hex
    simp only [if_pos hex] at h ⊢
    exact h
  · dsimp only [idx] at h hex
    simp only [if_neg hex] at h ⊢
    exact h

theorem fw_seed_rectangle_column_stage_weight {n L : ℕ}
    (hseed : 5*(4*6)+16*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (j : Fin 16) (c : Fin n) :
    fwSeedRectangleStageLineWeight hseed hs choice (fun x => x.2 = c) j =
      if ∃ i : Fin (4*6),
        RectanglePacking.firstColumn hs choice (fwSeedRectangle hseed (finProdFinEquiv (j,i))) = c ∨
        RectanglePacking.secondColumn hs choice (fwSeedRectangle hseed (finProdFinEquiv (j,i))) = c
      then 2 else 0 := by
  classical
  let idx := fun i : Fin (4*6) => fwSeedRectangle hseed (finProdFinEquiv (j,i))
  have hi : Function.Injective idx := seed_stage_index_injective hseed j
  unfold fwSeedRectangleStageLineWeight
  simp_rw [rectangle_column_pair_sum]
  have h := paired_indicator_sum (fun i => RectanglePacking.firstColumn hs choice (idx i))
    (fun i => RectanglePacking.secondColumn hs choice (idx i))
    ((RectanglePacking.firstColumn_injective hs choice).comp hi)
    ((RectanglePacking.secondColumn_injective hs choice).comp hi)
    (fun i k => RectanglePacking.firstColumn_ne_secondColumn hs choice (idx i) (idx k)) c
  by_cases hex : ∃ i, RectanglePacking.firstColumn hs choice (idx i) = c ∨ RectanglePacking.secondColumn hs choice (idx i) = c
  · dsimp only [idx] at h hex
    simp only [if_pos hex] at h ⊢
    exact h
  · dsimp only [idx] at h hex
    simp only [if_neg hex] at h ⊢
    exact h

end
end Sude
