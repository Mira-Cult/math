import Sude.NetworkSwitches

/-! Preserve every network pair unordered endpoints on the SAME toggle outcome. -/
namespace Sude
noncomputable section

theorem rowNetwork_toggle_subset_preserves_pair_endpoints {n : ℕ} {α : Type*} [DecidableEq α]
    (a : Cell n ≃ Fin (n * n)) (v : RowNetworkPairs α a) (S : Finset α) :
    ∃ b : Cell n ≃ Fin (n * n), RowNetworkOutcome v S b ∧
      ∀ k, (entry b (v.low k, v.column k) = entry a (v.low k, v.column k) ∧
        entry b (v.high k, v.column k) = entry a (v.high k, v.column k)) ∨
        (entry b (v.low k, v.column k) = entry a (v.high k, v.column k) ∧
        entry b (v.high k, v.column k) = entry a (v.low k, v.column k)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨a, ?_, ?_⟩
    · constructor
      · intro r; simp
      · intro c; rfl
      · rfl
      · rfl
      · intro c hc; rfl
    · intro k; exact Or.inl ⟨rfl, rfl⟩
  | @insert k S hk ih =>
    obtain ⟨b, hb, hpairs⟩ := ih
    have hslot_ne : ∀ l ∈ S, ∀ x y : Bool, rowNetworkSlot v (k, x) ≠ rowNetworkSlot v (l, y) := by
      intro l hl x y heq
      have hkl : k = l := congrArg Prod.fst (rowNetworkSlot_injective v heq)
      exact hk (hkl ▸ hl)
    have hlow : entry b (v.low k, v.column k) = entry a (v.low k, v.column k) := by
      apply hb.outside_fixed
      intro l hl
      exact ⟨by simpa [rowNetworkSlot] using hslot_ne l hl false false,
        by simpa [rowNetworkSlot] using hslot_ne l hl false true⟩
    have hhigh : entry b (v.high k, v.column k) = entry a (v.high k, v.column k) := by
      apply hb.outside_fixed
      intro l hl
      exact ⟨by simpa [rowNetworkSlot] using hslot_ne l hl true false,
        by simpa [rowNetworkSlot] using hslot_ne l hl true true⟩
    have hgap : entry b (v.high k, v.column k) = entry b (v.low k, v.column k) + v.gap k := by
      rw [hlow, hhigh]
      exact v.gap_at k
    let b' := swapPlacement b (v.low k, v.column k) (v.high k, v.column k)
    have hne : (v.low k, v.column k) ≠ (v.high k, v.column k) := by
      intro heq
      exact v.rows_ne k (congrArg Prod.fst heq)
    have hdiag := swapPlacement_diagonals_unchanged b _ _ hne
      (v.low_main k) (v.high_main k) (v.low_anti k) (v.high_anti k)
    have hnew : RowNetworkOutcome v (insert k S) b' := by
      constructor
      · intro r
        have hstep := verticalSwap_row_effect b (v.low k) (v.high k) (v.column k) r (v.rows_ne k)
        have hprev := hb.rows r
        have hgapZ : (entry b (v.high k, v.column k) : ℤ) =
            (entry b (v.low k, v.column k) : ℤ) + (v.gap k : ℤ) := by exact_mod_cast hgap
        simp only [Finset.sum_insert hk]
        change (rowSum b' r : ℤ) - (rowSum a r : ℤ) =
          ((if v.low k = r then (v.gap k : ℤ) else 0) -
            (if v.high k = r then (v.gap k : ℤ) else 0)) + ∑ l ∈ S, rowNetworkDelta v l r
        dsimp only [b'] at hstep ⊢
        split_ifs at hstep ⊢ <;> omega
      · intro c
        exact (verticalSwap_columns b (v.low k) (v.high k) (v.column k) (v.rows_ne k) c).trans (hb.columns c)
      · exact hdiag.1.trans hb.main
      · exact hdiag.2.trans hb.anti
      · intro c hc
        have hk' := hc k (Finset.mem_insert_self k S)
        have hS : ∀ l ∈ S, c ≠ (v.low l, v.column l) ∧ c ≠ (v.high l, v.column l) := by
          intro l hl
          exact hc l (Finset.mem_insert_of_mem hl)
        exact (swapPlacement_outside b _ _ c hk'.1 hk'.2).trans (hb.outside_fixed c hS)
    refine ⟨b', hnew, ?_⟩
    intro t
    by_cases htk : t = k
    · subst t
      right
      constructor
      · dsimp only [b']
        simpa [entry_swapPlacement, Equiv.swap_apply_left] using hhigh
      · dsimp only [b']
        simpa [entry_swapPlacement, Equiv.swap_apply_right] using hlow
    · have hdiff (x y : Bool) : rowNetworkSlot v (t,x) ≠ rowNetworkSlot v (k,y) := by
        intro heq
        exact htk (congrArg Prod.fst (rowNetworkSlot_injective v heq))
      have hlo : entry b' (v.low t, v.column t) = entry b (v.low t, v.column t) := by
        dsimp only [b']
        apply swapPlacement_outside
        · simpa [rowNetworkSlot] using hdiff false false
        · simpa [rowNetworkSlot] using hdiff false true
      have hhi : entry b' (v.high t, v.column t) = entry b (v.high t, v.column t) := by
        dsimp only [b']
        apply swapPlacement_outside
        · simpa [rowNetworkSlot] using hdiff true false
        · simpa [rowNetworkSlot] using hdiff true true
      rw [hlo, hhi]
      exact hpairs t



theorem columnNetwork_toggle_subset_preserves_pair_endpoints {n : ℕ} {α : Type*} [DecidableEq α]
    (a : Cell n ≃ Fin (n * n))
    (v : RowNetworkPairs α (LayerPacking.transposePlacement a)) (S : Finset α) :
    ∃ b : Cell n ≃ Fin (n * n), ColumnNetworkOutcome v S b ∧
      ∀ k, (entry b (v.column k, v.low k) = entry a (v.column k, v.low k) ∧
        entry b (v.column k, v.high k) = entry a (v.column k, v.high k)) ∨
        (entry b (v.column k, v.low k) = entry a (v.column k, v.high k) ∧
        entry b (v.column k, v.high k) = entry a (v.column k, v.low k)) := by
  obtain ⟨bt, hb, hpairs⟩ := rowNetwork_toggle_subset_preserves_pair_endpoints (LayerPacking.transposePlacement a) v S
  let b := LayerPacking.transposePlacement bt
  have hnew : ColumnNetworkOutcome v S b := by
    constructor
    · intro c
      simpa [b] using hb.rows c
    · intro r
      simpa [b] using hb.columns r
    · simpa [b] using hb.main
    · simpa [b] using hb.anti
    · intro c hc
      have hc' : ∀ k ∈ S, c.swap ≠ (v.low k, v.column k) ∧ c.swap ≠ (v.high k, v.column k) := by
        intro k hk
        have h := hc k hk
        constructor
        · intro heq
          apply h.1
          have hs := congrArg Prod.swap heq
          simpa using hs
        · intro heq
          apply h.2
          have hs := congrArg Prod.swap heq
          simpa using hs
      have hh := hb.outside_fixed c.swap hc'
      rcases c with ⟨i, j⟩
      simpa [b] using hh
  refine ⟨b, hnew, ?_⟩
  intro k
  simpa [b] using hpairs k

end
end Sude
