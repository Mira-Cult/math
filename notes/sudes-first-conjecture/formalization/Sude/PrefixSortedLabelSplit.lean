import Sude.PrefixLabelSelectionAdapter
import Sude.PrefixSplitMeanBounds
import Mathlib.Order.Interval.Finset.Fin

/-! Balanced lower/upper splitting of finite labelled numerical populations.
Coincident values remain distinct labels. -/
namespace Sude
noncomputable section

/-- A finite population of at least two labelled values admits a lower half
of exactly `card/2` labels. Every chosen value is at most every unchosen
value. This constructs no physical slot assignment. -/
theorem prefix_sorted_label_split {α : Type*} [DecidableEq α]
    (A : Finset α) (x : α → ℝ) (hA : 2 ≤ A.card) :
    ∃ T : Finset α, T ⊆ A ∧ T.card = A.card / 2 ∧
      (∀ a ∈ T, ∀ b ∈ A \ T, x a ≤ x b) := by
  classical
  let n := A.card
  have hn : 0 < n := by dsimp [n]; omega
  let e₀ : Fin n ≃ ↥A := A.equivFin.symm
  let v : Fin n → ℝ := fun i => x (e₀ i).1
  obtain ⟨e₁, he₁⟩ := prefix_sort_label_equiv v
  let e : Fin n ≃ ↥A := e₁.trans e₀
  have he : Monotone (fun i => x (e i).1) := he₁
  let j : Fin n := ⟨n / 2, by omega⟩
  let I : Finset (Fin n) := Finset.Iio j
  let f : Fin n → α := fun i => (e i).1
  let T : Finset α := I.image f
  have hf : Function.Injective f := by
    intro a b h
    apply e.injective
    exact Subtype.ext h
  have hTA : T ⊆ A := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact (e i).2
  have hcard : T.card = A.card / 2 := by
    rw [show T = I.image f from rfl, Finset.card_image_of_injective _ hf]
    simpa [I, j, n] using (Fin.card_Iio j)
  refine ⟨T, hTA, hcard, ?_⟩
  intro a ha b hb
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  have hbA := (Finset.mem_sdiff.mp hb).1
  have hbT := (Finset.mem_sdiff.mp hb).2
  let ib : Fin n := e.symm ⟨b, hbA⟩
  have hib : f ib = b := by simp [f, ib]
  have hnot : ib ∉ I := by
    intro h
    apply hbT
    exact Finset.mem_image.mpr ⟨ib, h, hib⟩
  have hi' : i < j := Finset.mem_Iio.mp hi
  have hib' : j ≤ ib := le_of_not_gt (by simpa [I] using hnot)
  have hle : i ≤ ib := le_trans (le_of_lt hi') hib'
  have h := he hle
  simpa [f, hib] using h


/-- Balanced labelled lower and upper halves are nonempty and their mean gap
lies in `[0,C]` under the original population's width bound. -/
theorem prefix_sorted_label_split_mean_gap {α : Type*} [DecidableEq α]
    (A : Finset α) (x : α → ℝ) (C : ℝ) (hA : 2 ≤ A.card)
    (hwidth : ∀ a ∈ A, ∀ b ∈ A, x b - x a ≤ C) :
    ∃ T : Finset α, T ⊆ A ∧ T.card = A.card / 2 ∧
      (A \ T).card = A.card - A.card / 2 ∧
      T.Nonempty ∧ (A \ T).Nonempty ∧
      (∀ a ∈ T, ∀ b ∈ A \ T, x a ≤ x b) ∧
      0 ≤ (∑ b ∈ A \ T, x b) / (A \ T).card - (∑ a ∈ T, x a) / T.card ∧
      (∑ b ∈ A \ T, x b) / (A \ T).card - (∑ a ∈ T, x a) / T.card ≤ C := by
  classical
  obtain ⟨T, hTA, hTcard, horder⟩ := prefix_sorted_label_split A x hA
  have hrest : (A \ T).card = A.card - A.card / 2 := by
    rw [Finset.card_sdiff_of_subset hTA, hTcard]
  have hTpos : 0 < T.card := by rw [hTcard]; omega
  have hRpos : 0 < (A \ T).card := by rw [hrest]; omega
  have hT := Finset.card_pos.mp hTpos
  have hR := Finset.card_pos.mp hRpos
  have hg := prefix_finite_split_mean_gap T (A \ T) x x C hT hR (by
    intro a ha b hb
    exact ⟨sub_nonneg.mpr (horder a ha b hb),
      hwidth a (hTA ha) b (Finset.mem_sdiff.mp hb).1⟩)
  exact ⟨T, hTA, hTcard, hrest, hT, hR, horder, hg⟩



end
end Sude
