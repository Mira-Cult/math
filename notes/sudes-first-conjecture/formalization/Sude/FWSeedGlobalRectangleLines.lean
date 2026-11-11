import Sude.FWSeedRectangleLineCounts

/-! Ordinary incidence and uniqueness of actual offset seed rectangles across stages.
This does not assert distinct-cell occupancy or any full-construction bound. -/
namespace Sude
noncomputable section

private theorem global_paired_indicator_sum {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
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


private theorem global_rect_row_sum {n L : ℕ} (hs : 2*L+1 ≤ n) (choice : Fin L → Bool)
    (i : Fin L) (r : Fin n) :
    (∑ p : Fin 2, rectanglePairWeight hs choice (fun c => c.1 = r) (i,p)) =
      (if RectanglePacking.firstRow hs i = r then (2:ℝ) else 0) +
      (if RectanglePacking.secondRow hs i = r then (2:ℝ) else 0) := by
  classical
  simp [Fin.sum_univ_two, rectanglePairWeight, prefixPairCorner, packedRectangleCorner]
  split_ifs <;> norm_num

private theorem global_rect_col_sum {n L : ℕ} (hs : 2*L+1 ≤ n) (choice : Fin L → Bool)
    (i : Fin L) (c : Fin n) :
    (∑ p : Fin 2, rectanglePairWeight hs choice (fun x => x.2 = c) (i,p)) =
      (if RectanglePacking.firstColumn hs choice i = c then (2:ℝ) else 0) +
      (if RectanglePacking.secondColumn hs choice i = c then (2:ℝ) else 0) := by
  classical
  simp [Fin.sum_univ_two, rectanglePairWeight, prefixPairCorner, packedRectangleCorner]
  split_ifs <;> norm_num

theorem fw_seed_global_row_rectangle_indicator {n L : ℕ}
    (hseed : 5 * (4*6) + 16 * (4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (r : Fin n) :
    (∑ j : Fin 16, ∑ i : Fin (4*6), ∑ p : Fin 2,
      rectanglePairWeight hs choice (fun c => c.1 = r)
        (fwSeedRectangle hseed (finProdFinEquiv (j,i)), p)) =
      if ∃ x : Fin 16 × Fin (4*6),
        RectanglePacking.firstRow hs (fwSeedRectangle hseed (finProdFinEquiv x)) = r ∨
        RectanglePacking.secondRow hs (fwSeedRectangle hseed (finProdFinEquiv x)) = r
      then 2 else 0 := by
  classical
  let idx := fun x : Fin 16 × Fin (4*6) => fwSeedRectangle hseed (finProdFinEquiv x)
  have hi : Function.Injective idx := (fwSeedRectangle_injective hseed).comp finProdFinEquiv.injective
  simp_rw [global_rect_row_sum]
  change (∑ j : Fin 16, ∑ i : Fin (4*6),
    ((if RectanglePacking.firstRow hs (idx (j,i)) = r then (2:ℝ) else 0) +
     (if RectanglePacking.secondRow hs (idx (j,i)) = r then (2:ℝ) else 0))) = _
  rw [← Fintype.sum_prod_type (fun x : Fin 16 × Fin (4*6) =>
    ((if RectanglePacking.firstRow hs (idx x) = r then (2:ℝ) else 0) +
     (if RectanglePacking.secondRow hs (idx x) = r then (2:ℝ) else 0)))]
  have h := global_paired_indicator_sum (fun x => RectanglePacking.firstRow hs (idx x))
    (fun x => RectanglePacking.secondRow hs (idx x))
    ((RectanglePacking.firstRow_injective hs).comp hi)
    ((RectanglePacking.secondRow_injective hs).comp hi)
    (fun a b => RectanglePacking.firstRow_ne_secondRow hs (idx a) (idx b)) r
  by_cases hex : ∃ x, RectanglePacking.firstRow hs (idx x) = r ∨ RectanglePacking.secondRow hs (idx x) = r
  · dsimp only [idx] at h hex
    simp only [if_pos hex] at h ⊢
    exact h
  · dsimp only [idx] at h hex
    simp only [if_neg hex] at h ⊢
    exact h

theorem fw_seed_global_column_rectangle_indicator {n L : ℕ}
    (hseed : 5 * (4*6) + 16 * (4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (c : Fin n) :
    (∑ j : Fin 16, ∑ i : Fin (4*6), ∑ p : Fin 2,
      rectanglePairWeight hs choice (fun x => x.2 = c)
        (fwSeedRectangle hseed (finProdFinEquiv (j,i)), p)) =
      if ∃ x : Fin 16 × Fin (4*6),
        RectanglePacking.firstColumn hs choice (fwSeedRectangle hseed (finProdFinEquiv x)) = c ∨
        RectanglePacking.secondColumn hs choice (fwSeedRectangle hseed (finProdFinEquiv x)) = c
      then 2 else 0 := by
  classical
  let idx := fun x : Fin 16 × Fin (4*6) => fwSeedRectangle hseed (finProdFinEquiv x)
  have hi : Function.Injective idx := (fwSeedRectangle_injective hseed).comp finProdFinEquiv.injective
  simp_rw [global_rect_col_sum]
  change (∑ j : Fin 16, ∑ i : Fin (4*6),
    ((if RectanglePacking.firstColumn hs choice (idx (j,i)) = c then (2:ℝ) else 0) +
     (if RectanglePacking.secondColumn hs choice (idx (j,i)) = c then (2:ℝ) else 0))) = _
  rw [← Fintype.sum_prod_type (fun x : Fin 16 × Fin (4*6) =>
    ((if RectanglePacking.firstColumn hs choice (idx x) = c then (2:ℝ) else 0) +
     (if RectanglePacking.secondColumn hs choice (idx x) = c then (2:ℝ) else 0)))]
  have h := global_paired_indicator_sum (fun x => RectanglePacking.firstColumn hs choice (idx x))
    (fun x => RectanglePacking.secondColumn hs choice (idx x))
    ((RectanglePacking.firstColumn_injective hs choice).comp hi)
    ((RectanglePacking.secondColumn_injective hs choice).comp hi)
    (fun a b => RectanglePacking.firstColumn_ne_secondColumn hs choice (idx a) (idx b)) c
  by_cases hex : ∃ x, RectanglePacking.firstColumn hs choice (idx x) = c ∨ RectanglePacking.secondColumn hs choice (idx x) = c
  · dsimp only [idx] at h hex
    simp only [if_pos hex] at h ⊢
    exact h
  · dsimp only [idx] at h hex
    simp only [if_neg hex] at h ⊢
    exact h


private theorem global_paired_hit_unique {α β : Type*} (f g : α → β)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ i k, f i ≠ g k) (r : β) (i k : α)
    (hi : f i = r ∨ g i = r) (hk : f k = r ∨ g k = r) : i = k := by
  rcases hi with hi | hi <;> rcases hk with hk | hk
  · exact hf (hi.trans hk.symm)
  · exact False.elim (hfg i k (hi.trans hk.symm))
  · exact False.elim (hfg k i (hk.trans hi.symm))
  · exact hg (hi.trans hk.symm)

theorem fw_seed_row_rectangle_stage_hit_unique {n L : ℕ}
    (hseed : 5 * (4*6) + 16 * (4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (r : Fin n) (j k : Fin 16) (i l : Fin (4*6))
    (hj : RectanglePacking.firstRow hs (fwSeedRectangle hseed (finProdFinEquiv (j,i))) = r ∨
      RectanglePacking.secondRow hs (fwSeedRectangle hseed (finProdFinEquiv (j,i))) = r)
    (hk : RectanglePacking.firstRow hs (fwSeedRectangle hseed (finProdFinEquiv (k,l))) = r ∨
      RectanglePacking.secondRow hs (fwSeedRectangle hseed (finProdFinEquiv (k,l))) = r) : j = k := by
  let idx := fun x : Fin 16 × Fin (4*6) => fwSeedRectangle hseed (finProdFinEquiv x)
  have hi : Function.Injective idx := (fwSeedRectangle_injective hseed).comp finProdFinEquiv.injective
  have h := global_paired_hit_unique (fun x => RectanglePacking.firstRow hs (idx x))
    (fun x => RectanglePacking.secondRow hs (idx x))
    ((RectanglePacking.firstRow_injective hs).comp hi)
    ((RectanglePacking.secondRow_injective hs).comp hi)
    (fun a b => RectanglePacking.firstRow_ne_secondRow hs (idx a) (idx b)) r (j,i) (k,l) hj hk
  exact congrArg Prod.fst h

theorem fw_seed_column_rectangle_stage_hit_unique {n L : ℕ}
    (hseed : 5 * (4*6) + 16 * (4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (c : Fin n) (j k : Fin 16) (i l : Fin (4*6))
    (hj : RectanglePacking.firstColumn hs choice (fwSeedRectangle hseed (finProdFinEquiv (j,i))) = c ∨
      RectanglePacking.secondColumn hs choice (fwSeedRectangle hseed (finProdFinEquiv (j,i))) = c)
    (hk : RectanglePacking.firstColumn hs choice (fwSeedRectangle hseed (finProdFinEquiv (k,l))) = c ∨
      RectanglePacking.secondColumn hs choice (fwSeedRectangle hseed (finProdFinEquiv (k,l))) = c) : j = k := by
  let idx := fun x : Fin 16 × Fin (4*6) => fwSeedRectangle hseed (finProdFinEquiv x)
  have hi : Function.Injective idx := (fwSeedRectangle_injective hseed).comp finProdFinEquiv.injective
  have h := global_paired_hit_unique (fun x => RectanglePacking.firstColumn hs choice (idx x))
    (fun x => RectanglePacking.secondColumn hs choice (idx x))
    ((RectanglePacking.firstColumn_injective hs choice).comp hi)
    ((RectanglePacking.secondColumn_injective hs choice).comp hi)
    (fun a b => RectanglePacking.firstColumn_ne_secondColumn hs choice (idx a) (idx b)) c (j,i) (k,l) hj hk
  exact congrArg Prod.fst h

end
end Sude
