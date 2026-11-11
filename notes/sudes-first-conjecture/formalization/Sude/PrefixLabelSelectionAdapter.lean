import Sude.PrefixGlobalSelection
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Sort

/-! Sorting labelled finite populations without merging equal numerical values. -/
namespace Sude
noncomputable section

/-- A finite labelled family admits an ordering by its numerical values.
The ordering is an equivalence of labels, including when values coincide. -/
theorem prefix_sort_label_equiv {n : ℕ} (x : Fin n → ℝ) :
    ∃ e : Fin n ≃ Fin n, Monotone (x ∘ e) := by
  classical
  let l := (List.finRange n).mergeSort (fun a b => decide (x a ≤ x b))
  have hp : l.Perm (List.finRange n) := List.mergeSort_perm _ _
  have hlen : l.length = n := by simpa using hp.length_eq
  have hn : l.Nodup := hp.nodup_iff.mpr (List.nodup_finRange n)
  have hm : ∀ a, a ∈ l := fun a => hp.mem_iff.mpr (List.mem_finRange a)
  let e : Fin n ≃ Fin n := (Fin.castOrderIso hlen.symm).toEquiv.trans
    (List.Nodup.getEquivOfForallMemList l hn hm)
  have hs : l.Pairwise (fun a b => x a ≤ x b) := by
    have h := List.pairwise_mergeSort
      (le := fun a b : Fin n => decide (x a ≤ x b))
      (by intro a b c hab hbc; exact decide_eq_true (le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
      (List.finRange n)
    simpa [l] using h
  refine ⟨e, ?_⟩
  intro a b hab
  change x (e a) ≤ x (e b)
  by_cases he : a = b
  · subst b; exact le_rfl
  · have hlt : a < b := lt_of_le_of_ne hab he
    have hcast : (Fin.cast hlen.symm a : Fin l.length) < Fin.cast hlen.symm b := hlt
    have hrel := hs.rel_get_of_lt hcast
    simpa [e] using hrel

/-- PD2 for arbitrary indexed stage populations: labels remain distinct, even
when several values coincide. -/
theorem prefix_global_indexed_select {J : Type*} [Fintype J] [DecidableEq J]
    (M : J → ℕ) (k : ℕ) (x : ∀ j, Fin (M j) → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hk : ∀ j, k ≤ M j)
    (hwidth : ∀ j (a b : Fin (M j)), x j b - x j a ≤ C) :
    ∃ T : ∀ j, Finset (Fin (M j)),
      (∀ j, (T j).card = k) ∧
      |(∑ j, ∑ i ∈ T j, x j i) -
        (k : ℝ) * ∑ j, ((∑ i, x j i) / M j)| ≤ C / 2 := by
  classical
  choose e he using fun j => prefix_sort_label_equiv (x j)
  let v : J → ℕ → ℝ := fun j i => if hi : i < M j then x j (e j ⟨i, hi⟩) else 0
  have hv : ∀ j i (hi : i < M j), v j i = x j (e j ⟨i, hi⟩) := by
    intro j i hi
    simp [v, hi]
  have hs : ∀ j i l, i ≤ l → l < M j → v j i ≤ v j l := by
    intro j i l hil hl
    have hi : i < M j := by omega
    rw [hv j i hi, hv j l hl]
    exact he j hil
  have hw : ∀ j i l, i < M j → l < M j → v j l - v j i ≤ C := by
    intro j i l hi hl
    rw [hv j i hi, hv j l hl]
    exact hwidth j _ _
  obtain ⟨T, hT, hbound⟩ := prefix_global_fixed_cardinality_select M k v C hC hk hs hw
  let S : ∀ j, Finset (Fin (M j)) := fun j => (T j).attach.image
    (fun i => e j ⟨i.1, Finset.mem_range.mp ((hT j).1 i.2)⟩)
  have hcard : ∀ j, (S j).card = k := by
    intro j
    unfold S
    rw [Finset.card_image_iff.mpr]
    · simpa using (hT j).2
    · intro a ha b hb hab
      apply Subtype.ext
      have h := (e j).injective hab
      exact congrArg Fin.val h
  have hsum : ∀ j, (∑ a ∈ S j, x j a) = ∑ i ∈ T j, v j i := by
    intro j
    unfold S
    rw [Finset.sum_image]
    · calc
        (∑ i ∈ (T j).attach, x j (e j ⟨i.1, Finset.mem_range.mp ((hT j).1 i.2)⟩)) =
            ∑ i ∈ (T j).attach, v j i.1 := by
              apply Finset.sum_congr rfl
              intro i hi
              exact (hv j i.1 _).symm
        _ = ∑ i ∈ T j, v j i := Finset.sum_attach (T j) (v j)
    · intro a ha b hb hab
      apply Subtype.ext
      exact congrArg Fin.val ((e j).injective hab)
  have hall : ∀ j, (∑ i ∈ Finset.range (M j), v j i) = ∑ i, x j i := by
    intro j
    rw [← Fin.sum_univ_eq_sum_range]
    calc
      (∑ i : Fin (M j), v j i.val) = ∑ i : Fin (M j), x j (e j i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hv j i.val i.isLt
      _ = ∑ i : Fin (M j), x j i := (e j).sum_comp (x j)
  refine ⟨S, hcard, ?_⟩
  simpa only [hsum, hall] using hbound

/-- PD2 for arbitrary finite labelled stage populations. Selection is by
labels, so coincident numerical values are never identified. -/
theorem prefix_global_finset_select {J α : Type*} [Fintype J] [DecidableEq J]
    [DecidableEq α] (s : J → Finset α) (k : ℕ) (x : J → α → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hk : ∀ j, k ≤ (s j).card)
    (hwidth : ∀ j, ∀ a ∈ s j, ∀ b ∈ s j, x j b - x j a ≤ C) :
    ∃ T : J → Finset α,
      (∀ j, T j ⊆ s j ∧ (T j).card = k) ∧
      |(∑ j, ∑ i ∈ T j, x j i) -
        (k : ℝ) * ∑ j, ((∑ i ∈ s j, x j i) / (s j).card)| ≤ C / 2 := by
  classical
  let e : ∀ j, Fin (s j).card ≃ ↥(s j) := fun j => (s j).equivFin.symm
  let v : ∀ j, Fin (s j).card → ℝ := fun j i => x j (e j i).1
  have hw : ∀ j (a b : Fin (s j).card), v j b - v j a ≤ C := by
    intro j a b
    exact hwidth j (e j a).1 (e j a).2 (e j b).1 (e j b).2
  obtain ⟨U, hU, hb⟩ := prefix_global_indexed_select (fun j => (s j).card) k v C hC hk hw
  let T : J → Finset α := fun j => (U j).image (fun i => (e j i).1)
  have hinj : ∀ j, Function.Injective (fun i : Fin (s j).card => (e j i).1) := by
    intro j a b h
    apply (e j).injective
    exact Subtype.ext h
  have hT : ∀ j, T j ⊆ s j ∧ (T j).card = k := by
    intro j
    constructor
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact (e j i).2
    · simpa [T, Finset.card_image_of_injective _ (hinj j)] using hU j
  have hsum : ∀ j, (∑ a ∈ T j, x j a) = ∑ i ∈ U j, v j i := by
    intro j
    simp [T, v, Finset.sum_image, (hinj j).injOn]
  have hall : ∀ j, (∑ i, v j i) = ∑ a ∈ s j, x j a := by
    intro j
    calc
      (∑ i, v j i) = ∑ a : ↥(s j), x j a.1 := by
        simpa [v] using (e j).sum_comp (fun a => x j a.1)
      _ = ∑ a ∈ s j, x j a := (Finset.sum_subtype (s j) (fun _ => Iff.rfl) (x j)).symm
  refine ⟨T, hT, ?_⟩
  simpa only [hsum, hall] using hb

end
end Sude
