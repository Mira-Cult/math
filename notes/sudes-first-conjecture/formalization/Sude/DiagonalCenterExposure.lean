import Sude.DiagonalFullStockCenter
import Sude.RegularFactorRF2
namespace Sude
noncomputable section

/-- Exact signed expectation shift when one labelled value is exposed.
The line contains that cell when `onLine` is true; k counts its other free cells. -/
theorem full_stock_center_exposure {α : Type*} [DecidableEq α]
    (stock T : Finset α) (value : α → ℝ) (x W : ℝ) (k : ℕ) (onLine : Bool)
    (hT : T ⊆ stock) (hcard : T.card = 1) (hpos : 0 < (stock \ T).card)
    (hx : (∑ v ∈ T, value v) = x)
    (hk : k ≤ (stock \ T).card)
    (hnear : |x - centralEntriesMean stock value| ≤ W / 2) :
    let ε : ℝ := if onLine then 1 else 0
    let μ := centralEntriesMean stock value
    let μ' := centralEntriesMean (stock \ T) value
    let N' : ℝ := (stock \ T).card
    (ε * x + k * μ') - (ε + k) * μ = (x - μ) * (ε - k / N') ∧
    |(ε * x + k * μ') - (ε + k) * μ| ≤ W / 2 := by
  classical
  dsimp only
  have hm := central_entries_actual_mean_update stock T value hT hpos
  rw [hx, hcard] at hm
  simp only [Nat.cast_one, one_mul] at hm
  have hden : (0 : ℝ) < (stock \ T).card := by exact_mod_cast hpos
  have hkreal : (k : ℝ) ≤ (stock \ T).card := by exact_mod_cast hk
  have hfrac : 0 ≤ (k : ℝ) / (stock \ T).card ∧ (k : ℝ) / (stock \ T).card ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_one hden).2 hkreal
  have hid : ((if onLine then (1 : ℝ) else 0) * x + k *
      centralEntriesMean (stock \ T) value) -
      ((if onLine then (1 : ℝ) else 0) + k) * centralEntriesMean stock value =
      (x - centralEntriesMean stock value) * ((if onLine then (1 : ℝ) else 0) - k / (stock \ T).card) := by
    rw [hm]
    ring
  constructor
  · exact hid
  · rw [hid, abs_mul]
    have hcoeff : |(if onLine then (1 : ℝ) else 0) - k / (stock \ T).card| ≤ 1 := by
      cases onLine <;> simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals rw [abs_le]; constructor <;> linarith [hfrac.1,hfrac.2]
    have hnear0 : 0 ≤ W / 2 := le_trans (abs_nonneg _) hnear
    calc
      _ ≤ (W / 2) * 1 := mul_le_mul hnear hcoeff (abs_nonneg _) hnear0
      _ = W / 2 := by ring

theorem center_free_line_le_unused {n : ℕ} (b : Cell n ≃ Fin (n * n))
    (reserved line : Finset (Cell n)) :
    (line \ reserved).card ≤ (actualUnusedPool b reserved).card := by
  classical
  have hsub : line \ reserved ⊆ (Finset.univ : Finset (Cell n)) \ reserved := by
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hz).2⟩
  have h := Finset.card_le_card hsub
  unfold actualUnusedPool
  rw [Finset.card_image_of_injective _ (entryPool b).injective]
  exact h

theorem center_free_line_card_split {n : ℕ} (reserved line : Finset (Cell n))
    (center : Cell n) (hcenter : center ∉ reserved) :
    (line \ reserved).card = (if center ∈ line then 1 else 0) +
      (line \ (reserved ∪ {center})).card := by
  classical
  by_cases hc : center ∈ line
  · have hnot : center ∉ line \ (reserved ∪ {center}) := by simp
    have heq : line \ reserved = insert center (line \ (reserved ∪ {center})) := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
      by_cases he : z = center
      · subst z; simp [hc, hcenter]
      · simp [he]
    rw [heq, Finset.card_insert_of_notMem hnot]
    simp [hc, Nat.add_comm]
  · have heq : line \ reserved = line \ (reserved ∪ {center}) := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
      by_cases he : z = center
      · subst z; simp [hc]
      · simp [he]
    simp [hc, heq]

theorem center_fixed_line_sum_split {n : ℕ} (a b : Cell n ≃ Fin (n * n))
    (reserved line : Finset (Cell n)) (center : Cell n) (hcenter : center ∉ reserved)
    (hfixed : ∀ z ∈ reserved, entry b z = entry a z) :
    (∑ z ∈ line ∩ (reserved ∪ {center}), (entry b z : ℝ)) =
      (∑ z ∈ line ∩ reserved, (entry a z : ℝ)) +
        if center ∈ line then (entry b center : ℝ) else 0 := by
  classical
  have hdis : Disjoint reserved ({center} : Finset (Cell n)) := by simpa using hcenter
  rw [factor_line_fixed_sum a b reserved {center} line hdis hfixed]
  by_cases hc : center ∈ line
  · have heq : line ∩ ({center} : Finset (Cell n)) = {center} := by ext z; simp [hc]
    simp [heq, hc]
  · have heq : line ∩ ({center} : Finset (Cell n)) = ∅ := by ext z; simp [hc]
    simp [heq, hc]


/-- Choose and place a center so that every labelled cell set's conditional
completion expectation changes by at most X/2. The old and new means are
of the exact unused pools on the corresponding squares. -/
theorem actual_center_preserves_line_expectations {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (center : Cell n) (hcenter : center ∉ reserved)
    (hstock : 1 < (actualUnusedPool a reserved).card) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      0 < (actualUnusedPool b (reserved ∪ {center})).card ∧
      ∀ line : Finset (Cell n),
        |((∑ z ∈ line ∩ (reserved ∪ {center}), (entry b z : ℝ)) +
            ((line \ (reserved ∪ {center})).card : ℝ) *
              centralEntriesMean (actualUnusedPool b (reserved ∪ {center})) centralPoolValue) -
          ((∑ z ∈ line ∩ reserved, (entry a z : ℝ)) +
            ((line \ reserved).card : ℝ) *
              centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (poolMaximum n : ℝ) / 2 := by
  classical
  obtain ⟨b, T, hT, hTc, himage, hfixed, hremain, hnear⟩ :=
    actual_unused_pool_place_center a reserved center hcenter (by omega)
  have hcard := Finset.card_sdiff_add_card_eq_card hT
  have hpos : 0 < (actualUnusedPool a reserved \ T).card := by omega
  have hsum : (∑ x ∈ T, centralPoolValue x) = (entry b center : ℝ) := by
    have h := finite_population_sum b {center} T himage
    simpa using h.symm
  refine ⟨b, hfixed, hremain ▸ hpos, ?_⟩
  intro line
  let k := (line \ (reserved ∪ {center})).card
  have hk : k ≤ (actualUnusedPool a reserved \ T).card := by
    rw [← hremain]
    exact center_free_line_le_unused b (reserved ∪ {center}) line
  have hbound := (full_stock_center_exposure (actualUnusedPool a reserved) T centralPoolValue
    (entry b center) (poolMaximum n) k (decide (center ∈ line)) hT hTc hpos hsum hk hnear).2
  have hf := center_fixed_line_sum_split a b reserved line center hcenter hfixed
  have hc := center_free_line_card_split reserved line center hcenter
  have hcR : ((line \ reserved).card : ℝ) =
      (if center ∈ line then (1 : ℝ) else 0) + k := by
    by_cases h : center ∈ line <;> simp [h, k] at hc ⊢ <;> exact_mod_cast hc
  rw [hf, hcR, hremain]
  by_cases hline : center ∈ line <;> simp [hline, k] at hbound ⊢ <;>
    convert hbound using 1 <;> ring_nf

end
end Sude
