import Sude.CentralWindow
import Mathlib.Data.Finset.Sort

/-! Apply CC2's sorted-window argument to an actual finite central stock. -/
namespace Sude
noncomputable section

/-- The increasing enumeration of a finite real stock, total outside its range. -/
def centralOrder (s : Finset ℝ) (i : ℕ) : ℝ :=
  if h : i < s.card then s.orderEmbOfFin rfl ⟨i, h⟩ else 0

theorem centralOrder_injective_on (s : Finset ℝ) :
    ∀ i < s.card, ∀ j < s.card, centralOrder s i = centralOrder s j → i = j := by
  intro i hi j hj h
  have he : s.orderEmbOfFin rfl ⟨i, hi⟩ = s.orderEmbOfFin rfl ⟨j, hj⟩ := by
    simpa [centralOrder, hi, hj] using h
  exact congrArg Fin.val ((s.orderEmbOfFin rfl).injective he)

theorem centralOrder_monotone_on (s : Finset ℝ) :
    ∀ i j, i ≤ j → j < s.card → centralOrder s i ≤ centralOrder s j := by
  intro i j hij hj
  have hi : i < s.card := lt_of_le_of_lt hij hj
  have h := (s.orderEmbOfFin rfl).monotone (show (⟨i, hi⟩ : Fin s.card) ≤ ⟨j, hj⟩ from hij)
  simpa [centralOrder, hi, hj] using h

theorem centralOrder_image (s : Finset ℝ) : (Finset.range s.card).image (centralOrder s) = s := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' := Finset.mem_range.mp hi
    simp [centralOrder, hi', Finset.orderEmbOfFin_mem]
  · intro hx
    have hx' : x ∈ Set.range (s.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hx
    obtain ⟨i, hi⟩ := hx'
    refine Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, ?_⟩
    simpa [centralOrder, i.isLt] using hi

/-- Counting any condition on the ordered indices is exactly counting the
corresponding elements of the original stock. -/
theorem centralOrder_filter_card (s : Finset ℝ) (P : ℝ → Prop) [DecidablePred P] :
    ((Finset.range s.card).filter (fun i => P (centralOrder s i))).card =
      (s.filter P).card := by
  classical
  let I := (Finset.range s.card).filter (fun i => P (centralOrder s i))
  have hinj : Set.InjOn (centralOrder s) (↑I : Set ℕ) := by
    intro i hi j hj h
    exact centralOrder_injective_on s i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
      j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) h
  have himage : I.image (centralOrder s) = s.filter P := by
    rw [← Finset.filter_image, centralOrder_image]
  rw [← himage, Finset.card_image_iff.mpr hinj]

/-- CC2 for an actual central stock: the two outer intervals each contain
at least `q` still-unused values and the current mean lies strictly between
them. The selected subset has exact size and sum error at most `η`.
The case `q = 0` is included. -/
theorem central_stock_select (s : Finset ℝ) (q : ℕ) (c η ν : ℝ)
    (hη : 0 ≤ η) (hmid : c - η / 2 < ν ∧ ν < c + η / 2)
    (hcentral : ∀ x ∈ s, |x - c| ≤ η)
    (hlow : q ≤ (s.filter (fun x => c - η < x ∧ x ≤ c - η / 2)).card)
    (hhigh : q ≤ (s.filter (fun x => c + η / 2 < x ∧ x ≤ c + η)).card) :
    ∃ T : Finset ℝ, T ⊆ s ∧ T.card = q ∧
      |(∑ x ∈ T, x) - (q : ℝ) * ν| ≤ η := by
  classical
  have hq : q ≤ s.card := hlow.trans (Finset.card_filter_le _ _)
  have hlow' : q ≤ (s.filter (fun x => x ≤ ν)).card := by
    apply hlow.trans
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hxs, _, hxhigh⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxs, by linarith [hmid.1]⟩
  have hhigh' : q ≤ (s.filter (fun x => ν ≤ x)).card := by
    apply hhigh.trans
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hxs, hxlow, _⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxs, by linarith [hmid.2]⟩
  have hinterval : ∀ i < s.card, |centralOrder s i - c| ≤ η := by
    intro i hi
    apply hcentral
    simp [centralOrder, hi, Finset.orderEmbOfFin_mem]
  have hlow'' : q ≤ ((Finset.range s.card).filter (fun i => centralOrder s i ≤ ν)).card := by
    rw [centralOrder_filter_card s (fun x : ℝ => x ≤ ν)]
    exact hlow'
  have hhigh'' : q ≤ ((Finset.range s.card).filter (fun i => ν ≤ centralOrder s i)).card := by
    rw [centralOrder_filter_card s (fun x : ℝ => ν ≤ x)]
    exact hhigh'
  obtain ⟨T, hT, hc, herr⟩ := central_window_select_from_counts (centralOrder s) s.card q c η ν
    hη hq (centralOrder_injective_on s) (centralOrder_monotone_on s) hinterval hlow'' hhigh''
  exact ⟨T, by simpa [centralOrder_image] using hT, hc, herr⟩

/-- The selected values are drawn from the actual unused stock, with the
two outer counts measured before the selection. The empty-batch case does
not require the current mean to lie in the inner interval. -/
theorem central_unused_stock_select (unused : Finset ℝ) (q : ℕ) (c η ν : ℝ)
    (hη : 0 ≤ η) (hmid : q ≠ 0 → c - η / 2 < ν ∧ ν < c + η / 2)
    (hlow : q ≤ (unused.filter (fun x => c - η < x ∧ x ≤ c - η / 2)).card)
    (hhigh : q ≤ (unused.filter (fun x => c + η / 2 < x ∧ x ≤ c + η)).card) :
    ∃ T : Finset ℝ, T ⊆ unused ∧ T.card = q ∧
      (∀ x ∈ T, |x - c| ≤ η) ∧
      |(∑ x ∈ T, x) - (q : ℝ) * ν| ≤ η := by
  classical
  by_cases hq : q = 0
  · refine ⟨∅, Finset.empty_subset _, ?_, ?_, ?_⟩
    · simp [hq]
    · simp
    · simp [hq, hη]
  · let central := unused.filter (fun x => |x - c| ≤ η)
    have hcentral : ∀ x ∈ central, |x - c| ≤ η := by
      intro x hx
      exact (Finset.mem_filter.mp hx).2
    have hlo : q ≤ (central.filter (fun x => c - η < x ∧ x ≤ c - η / 2)).card := by
      apply hlow.trans
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hu, hl, hr⟩ := Finset.mem_filter.mp hx
      have hc : |x - c| ≤ η := by rw [abs_le]; constructor <;> linarith
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hu, hc⟩, hl, hr⟩
    have hhi : q ≤ (central.filter (fun x => c + η / 2 < x ∧ x ≤ c + η)).card := by
      apply hhigh.trans
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hu, hl, hr⟩ := Finset.mem_filter.mp hx
      have hc : |x - c| ≤ η := by rw [abs_le]; constructor <;> linarith
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hu, hc⟩, hl, hr⟩
    obtain ⟨T, hT, hcard, herr⟩ := central_stock_select central q c η ν
      hη (hmid hq) hcentral hlo hhi
    refine ⟨T, ?_, hcard, ?_, herr⟩
    · intro x hx
      exact (Finset.mem_filter.mp (hT hx)).1
    · intro x hx
      exact hcentral x (hT hx)

/-- CC8's exact change of mean after deleting a distinct selected batch.
The previous mean is characterized by the actual stock sum, and the
denominator is the positive number of entries that remain. -/
theorem central_stock_mean_update (unused chosen : Finset ℝ) (μ : ℝ)
    (hsub : chosen ⊆ unused) (hpos : 0 < (unused \ chosen).card)
    (hsum : (∑ x ∈ unused, x) = (unused.card : ℝ) * μ) :
    (∑ x ∈ unused \ chosen, x) / ((unused \ chosen).card : ℝ) =
      μ - ((∑ x ∈ chosen, x) - (chosen.card : ℝ) * μ) /
        ((unused \ chosen).card : ℝ) := by
  have hcard : ((unused \ chosen).card : ℝ) + (chosen.card : ℝ) = (unused.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hsub
  have hsum' := Finset.sum_sdiff (f := fun x : ℝ => x) hsub
  have hne : ((unused \ chosen).card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
  have hcardmul := congrArg (fun x : ℝ => x * μ) hcard
  field_simp
  nlinarith [hcardmul]

/-- The same selection for an actual finite family of labelled entries.
Injectivity is checked on the unused family, so no two selected labels
can stand for the same value. -/
theorem central_unused_entries_select {α : Type*} [DecidableEq α]
    (unused : Finset α) (value : α → ℝ) (hinj : Set.InjOn value (↑unused : Set α))
    (q : ℕ) (c η ν : ℝ) (hη : 0 ≤ η)
    (hmid : q ≠ 0 → c - η / 2 < ν ∧ ν < c + η / 2)
    (hlow : q ≤ (unused.filter (fun a => c - η < value a ∧ value a ≤ c - η / 2)).card)
    (hhigh : q ≤ (unused.filter (fun a => c + η / 2 < value a ∧ value a ≤ c + η)).card) :
    ∃ T : Finset α, T ⊆ unused ∧ T.card = q ∧
      (∀ a ∈ T, |value a - c| ≤ η) ∧
      |(∑ a ∈ T, value a) - (q : ℝ) * ν| ≤ η := by
  classical
  let stock := unused.image value
  have hfilter (P : ℝ → Prop) [DecidablePred P] :
      (stock.filter P).card = (unused.filter (fun a => P (value a))).card := by
    have hi : Set.InjOn value (↑(unused.filter (fun a => P (value a))) : Set α) := by
      intro a ha b hb heq
      exact hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 heq
    rw [show stock = unused.image value from rfl, Finset.filter_image,
      Finset.card_image_iff.mpr hi]
  have hlow' : q ≤ (stock.filter (fun x => c - η < x ∧ x ≤ c - η / 2)).card := by
    rw [hfilter]
    exact hlow
  have hhigh' : q ≤ (stock.filter (fun x => c + η / 2 < x ∧ x ≤ c + η)).card := by
    rw [hfilter]
    exact hhigh
  obtain ⟨selected, hselected, hcard, hcentral, herr⟩ :=
    central_unused_stock_select stock q c η ν hη hmid hlow' hhigh'
  let T := unused.filter (fun a => value a ∈ selected)
  have hT : T ⊆ unused := Finset.filter_subset _ _
  have hi : Set.InjOn value (↑T : Set α) := fun a ha b hb heq => hinj (hT ha) (hT hb) heq
  have himage : T.image value = selected := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp ha).2
    · intro hx
      obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp (hselected hx)
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, heq ▸ hx⟩, heq⟩
  refine ⟨T, hT, ?_, ?_, ?_⟩
  · rw [← Finset.card_image_iff.mpr hi, himage]
    exact hcard
  · intro a ha
    exact hcentral (value a) (Finset.mem_filter.mp ha).2
  · rw [← himage, Finset.sum_image hi] at herr
    exact herr

/-- Deleting any entries reduces either outer stock by at most the total
number deleted, even if every deleted entry is in that stock. -/
theorem central_stock_after_deletion {α : Type*} [DecidableEq α]
    (unused removed : Finset α) (P : α → Prop) [DecidablePred P] (q : ℕ)
    (hstock : q + removed.card ≤ (unused.filter P).card) :
    q ≤ ((unused \ removed).filter P).card := by
  have h := Finset.card_le_card_sdiff_add_card (s := unused.filter P) (t := removed)
  have heq : (unused.filter P) \ removed = (unused \ removed).filter P := by
    ext x
    simp [and_assoc, and_comm]
  rw [heq] at h
  omega

/-- CC8 for arbitrary labelled entries, using their actual real values. -/
theorem central_entries_mean_update {α : Type*} [DecidableEq α]
    (unused chosen : Finset α) (value : α → ℝ) (μ : ℝ)
    (hsub : chosen ⊆ unused) (hpos : 0 < (unused \ chosen).card)
    (hsum : (∑ a ∈ unused, value a) = (unused.card : ℝ) * μ) :
    (∑ a ∈ unused \ chosen, value a) / ((unused \ chosen).card : ℝ) =
      μ - ((∑ a ∈ chosen, value a) - (chosen.card : ℝ) * μ) /
        ((unused \ chosen).card : ℝ) := by
  have hcard : ((unused \ chosen).card : ℝ) + (chosen.card : ℝ) = (unused.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hsub
  have hsum' := Finset.sum_sdiff (f := value) hsub
  have hne : ((unused \ chosen).card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
  have hcardmul := congrArg (fun x : ℝ => x * μ) hcard
  field_simp
  nlinarith [hcardmul]

def centralEntriesMean {α : Type*} (unused : Finset α) (value : α → ℝ) : ℝ :=
  (∑ a ∈ unused, value a) / (unused.card : ℝ)

/-- The mean update with both means calculated from the actual stocks. -/
theorem central_entries_actual_mean_update {α : Type*} [DecidableEq α]
    (unused chosen : Finset α) (value : α → ℝ)
    (hsub : chosen ⊆ unused) (hpos : 0 < (unused \ chosen).card) :
    centralEntriesMean (unused \ chosen) value = centralEntriesMean unused value -
      ((∑ a ∈ chosen, value a) - (chosen.card : ℝ) * centralEntriesMean unused value) /
        ((unused \ chosen).card : ℝ) := by
  have hsubset : unused \ chosen ⊆ unused := Finset.sdiff_subset
  have hpos' : 0 < unused.card := lt_of_lt_of_le hpos (Finset.card_le_card hsubset)
  have hne : (unused.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos')
  have hsum : (∑ a ∈ unused, value a) = (unused.card : ℝ) * centralEntriesMean unused value := by
    unfold centralEntriesMean
    field_simp
  exact central_entries_mean_update unused chosen value (centralEntriesMean unused value)
    hsub hpos hsum

end
end Sude
