import Sude.EvenGrid
import Sude.PairSwitch

/-! Physical row-transfer reservoirs with disjoint pair supports. The input
    pair population is a hypothesis; its finite certificate remains open. -/
namespace Sude
noncomputable section

/-- The actual cells and entries of a family of vertical correction pairs.
    Injective columns ensure the physical supports are disjoint. -/
structure VerticalPairSystem {n : ℕ} (a : Cell n ≃ Fin (n * n)) (P : ℕ) where
  lowRow : Fin n
  highRow : Fin n
  rows_ne : lowRow ≠ highRow
  column : ℕ → Fin n
  column_injective : ∀ j k, j < P → k < P → column j = column k → j = k
  gap : ℕ → ℕ
  gap_at : ∀ j, j < P → entry a (highRow, column j) = entry a (lowRow, column j) + gap j
  low_off_main : ∀ j, j < P → (lowRow, column j) ∉ mainCells n
  high_off_main : ∀ j, j < P → (highRow, column j) ∉ mainCells n
  low_off_anti : ∀ j, j < P → (lowRow, column j) ∉ antiCells n
  high_off_anti : ∀ j, j < P → (highRow, column j) ∉ antiCells n

/-- A swap in one column fixes both cells of any other column. -/
theorem verticalSwap_other_column {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j k l r : Fin n) (h : l ≠ k) :
    entry (swapPlacement a (i, k) (j, k)) (r, l) = entry a (r, l) := by
  apply swapPlacement_outside
  · intro heq; exact h (congrArg Prod.snd heq)
  · intro heq; exact h (congrArg Prod.snd heq)

/-- All invariants after toggling the indexed subset. The still-untoggled
    pairs retain their original actual entries, so induction cannot reuse
    an abstract capacity after changing its physical realization. -/
structure VerticalOutcome {n P : ℕ} {a : Cell n ≃ Fin (n * n)}
    (v : VerticalPairSystem a P) (reserved : Finset (Cell n))
    (S : Finset ℕ) (b : Cell n ≃ Fin (n * n)) : Prop where
  rows : ∀ r,
    (rowSum b r : ℤ) - (rowSum a r : ℤ) =
      (if v.lowRow = r then ∑ k ∈ S, (v.gap k : ℤ) else 0) -
      (if v.highRow = r then ∑ k ∈ S, (v.gap k : ℤ) else 0)
  columns : ∀ r, columnSum b r = columnSum a r
  main : mainSum b = mainSum a
  anti : antiSum b = antiSum a
  reserved_fixed : ∀ c ∈ reserved, entry b c = entry a c
  unused_fixed : ∀ k, k < P → k ∉ S →
    entry b (v.lowRow, v.column k) = entry a (v.lowRow, v.column k) ∧
      entry b (v.highRow, v.column k) = entry a (v.highRow, v.column k)

/-- Every finite subset of an actual pair family can be switched, with all
    line effects, disjointness and reservations accounted for. -/
theorem verticalPairs_toggle_subset {n P : ℕ} (a : Cell n ≃ Fin (n * n))
    (v : VerticalPairSystem a P) (reserved : Finset (Cell n))
    (hreserved : ∀ k, k < P → ∀ c ∈ reserved,
      c ≠ (v.lowRow, v.column k) ∧ c ≠ (v.highRow, v.column k))
    (S : Finset ℕ) (hS : S ⊆ Finset.range P) :
    ∃ b : Cell n ≃ Fin (n * n), VerticalOutcome v reserved S b := by
  classical
  revert hS
  induction S using Finset.induction_on with
  | empty =>
    intro hS
    refine ⟨a, ?_⟩
    constructor
    · intro r
      simp
    · intro r
      rfl
    · rfl
    · rfl
    · intro c hc
      rfl
    · intro k hk hnot
      exact ⟨rfl, rfl⟩
  | @insert k S hk ih =>
    intro hS
    have hkP : k < P := by
      have h := hS (Finset.mem_insert_self k S)
      simpa using h
    have hsub : S ⊆ Finset.range P := by
      intro t ht
      exact hS (Finset.mem_insert_of_mem ht)
    obtain ⟨b, hb⟩ := ih hsub
    have hkeep := hb.unused_fixed k hkP hk
    have hgap : entry b (v.highRow, v.column k) = entry b (v.lowRow, v.column k) + v.gap k := by
      rw [hkeep.1, hkeep.2]
      exact v.gap_at k hkP
    let b' := swapPlacement b (v.lowRow, v.column k) (v.highRow, v.column k)
    have hne : (v.lowRow, v.column k) ≠ (v.highRow, v.column k) := by
      intro h
      exact v.rows_ne (congrArg Prod.fst h)
    have hdiag := swapPlacement_diagonals_unchanged b _ _ hne
      (v.low_off_main k hkP) (v.high_off_main k hkP)
      (v.low_off_anti k hkP) (v.high_off_anti k hkP)
    refine ⟨b', ?_⟩
    constructor
    · intro r
      have hstep := verticalSwap_row_effect b v.lowRow v.highRow (v.column k) r v.rows_ne
      have hprev := hb.rows r
      have hgapZ : (entry b (v.highRow, v.column k) : ℤ) =
          (entry b (v.lowRow, v.column k) : ℤ) + (v.gap k : ℤ) := by
        exact_mod_cast hgap
      simp only [Finset.sum_insert hk]
      dsimp [b'] at hstep ⊢
      split_ifs at hstep hprev ⊢ <;> omega
    · intro r
      exact (verticalSwap_columns b v.lowRow v.highRow (v.column k) v.rows_ne r).trans (hb.columns r)
    · exact hdiag.1.trans hb.main
    · exact hdiag.2.trans hb.anti
    · intro c hc
      have haway := hreserved k hkP c hc
      exact (swapPlacement_outside b _ _ c haway.1 haway.2).trans (hb.reserved_fixed c hc)
    · intro l hlP hlnot
      have hlnotS : l ∉ S := by
        intro hl
        exact hlnot (Finset.mem_insert_of_mem hl)
      have hlne : l ≠ k := by
        intro h
        subst l
        exact hlnot (Finset.mem_insert_self k S)
      have hcne : v.column l ≠ v.column k := by
        intro hc
        exact hlne (v.column_injective l k hlP hkP hc)
      have hold := hb.unused_fixed l hlP hlnotS
      exact ⟨(verticalSwap_other_column b v.lowRow v.highRow (v.column k) (v.column l)
          v.lowRow hcne).trans hold.1,
        (verticalSwap_other_column b v.lowRow v.highRow (v.column k) (v.column l)
          v.highRow hcne).trans hold.2⟩

/-- Any proved complete grid on supplied physical pairs gives an actual row
    transfer, including grids extended by fresh bridge gaps. -/
theorem vertical_grid_correction {n P : ℕ} (a : Cell n ≃ Fin (n * n))
    (v : VerticalPairSystem a P) (reserved : Finset (Cell n))
    (hreserved : ∀ k, k < P → ∀ c ∈ reserved,
      c ≠ (v.lowRow, v.column k) ∧ c ≠ (v.highRow, v.column k))
    (labels : Finset ℕ) (hlabels : labels ⊆ Finset.range P) (R : ℕ)
    (hgrid : CompleteEvenGrid labels v.gap R)
    (t : ℕ) (heven : 2 ∣ t) (hbound : t ≤ R) :
    ∃ S : Finset ℕ, S ⊆ labels ∧ (∑ k ∈ S, v.gap k) = t ∧
      ∃ b : Cell n ≃ Fin (n * n), VerticalOutcome v reserved S b ∧
        (rowSum b v.lowRow : ℤ) = (rowSum a v.lowRow : ℤ) + t ∧
        (rowSum b v.highRow : ℤ) = (rowSum a v.highRow : ℤ) - t ∧
        (∀ r, r ≠ v.lowRow → r ≠ v.highRow → rowSum b r = rowSum a r) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  obtain ⟨S, hS, hsum⟩ := hgrid t hbound heven
  obtain ⟨b, hb⟩ := verticalPairs_toggle_subset a v reserved hreserved S (hS.trans hlabels)
  have hsumZ : (∑ k ∈ S, (v.gap k : ℤ)) = (t : ℤ) := by
    exact_mod_cast hsum
  refine ⟨S, hS, hsum, b, hb, ?_, ?_, ?_, entry_range _, entry_injective _⟩
  · have hr := hb.rows v.lowRow
    simp only [if_neg (Ne.symm v.rows_ne), sub_zero] at hr
    rw [hsumZ] at hr
    simp only [if_true] at hr
    omega
  · have hr := hb.rows v.highRow
    simp only [if_neg v.rows_ne, zero_sub] at hr
    rw [hsumZ] at hr
    simp only [if_true] at hr
    omega
  · intro r hlow hhigh
    have hr := hb.rows r
    simp [Ne.symm hlow, Ne.symm hhigh] at hr
    omega

/-- The FPF1 complete grid is realized by actual disjoint swaps, not an
    abstract flow. Existing reservations, both diagonals and every column
    are preserved; all unselected pair entries remain available. -/
theorem vertical_binary_correction {n P : ℕ} (a : Cell n ≃ Fin (n * n))
    (v : VerticalPairSystem a P) (reserved : Finset (Cell n))
    (hreserved : ∀ k, k < P → ∀ c ∈ reserved,
      c ≠ (v.lowRow, v.column k) ∧ c ≠ (v.highRow, v.column k))
    (hgap : ∀ k, k < P → v.gap k = 2 ^ (k + 1))
    (t : ℕ) (heven : 2 ∣ t) (hbound : t ≤ 2 ^ (P + 1) - 2) :
    ∃ S : Finset ℕ, S ⊆ Finset.range P ∧ (∑ k ∈ S, v.gap k) = t ∧
      ∃ b : Cell n ≃ Fin (n * n), VerticalOutcome v reserved S b ∧
        (rowSum b v.lowRow : ℤ) = (rowSum a v.lowRow : ℤ) + t ∧
        (rowSum b v.highRow : ℤ) = (rowSum a v.highRow : ℤ) - t ∧
        (∀ r, r ≠ v.lowRow → r ≠ v.highRow → rowSum b r = rowSum a r) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  obtain ⟨S, hS, hbinary⟩ := binary_even_grid P t heven hbound
  have hsum : (∑ k ∈ S, v.gap k) = t := by
    calc
      (∑ k ∈ S, v.gap k) = ∑ k ∈ S, 2 ^ (k + 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hgap k (Finset.mem_range.mp (hS hk))
      _ = t := hbinary
  obtain ⟨b, hb⟩ := verticalPairs_toggle_subset a v reserved hreserved S hS
  have hsumZ : (∑ k ∈ S, (v.gap k : ℤ)) = (t : ℤ) := by
    exact_mod_cast hsum
  refine ⟨S, hS, hsum, b, hb, ?_, ?_, ?_, entry_range _, entry_injective _⟩
  · have hr := hb.rows v.lowRow
    simp only [if_neg (Ne.symm v.rows_ne), sub_zero] at hr
    rw [hsumZ] at hr
    simp only [if_true] at hr
    omega
  · have hr := hb.rows v.highRow
    simp only [if_neg v.rows_ne, zero_sub] at hr
    rw [hsumZ] at hr
    simp only [if_true] at hr
    omega
  · intro r hlow hhigh
    have hr := hb.rows r
    simp [Ne.symm hlow, Ne.symm hhigh] at hr
    omega

end
end Sude
