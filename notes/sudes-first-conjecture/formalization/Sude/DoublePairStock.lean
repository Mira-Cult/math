import Sude.PrimePairMatching
import Mathlib.Combinatorics.Pigeonhole

/-! FC2K5: repeated differences from two finite stocks, with exact
depletion and disjoint endpoints. No numerical stock bound is established. -/
namespace Sude
noncomputable section

/-- Two cross-pairs with the same positive gap. -/
structure DoublePair where
  low₁ : ℕ
  low₂ : ℕ
  high₁ : ℕ
  high₂ : ℕ
  deriving DecidableEq

def DoublePair.valid (b : DoublePair) (low high : Finset ℕ) : Prop :=
  b.low₁ ∈ low ∧ b.low₂ ∈ low ∧ b.high₁ ∈ high ∧ b.high₂ ∈ high ∧
  b.low₁ ≠ b.low₂ ∧ b.high₁ ≠ b.high₂ ∧ b.low₁ < b.high₁ ∧
  b.low₂ < b.high₂ ∧ b.high₁ - b.low₁ = b.high₂ - b.low₂

def DoublePair.footprint (b : DoublePair) : Finset ℕ :=
  {b.low₁, b.low₂, b.high₁, b.high₂}

/-- More cross-pairs than difference labels force two distinct pairs with
the same difference. Strictly ordered sides ensure all four endpoints differ. -/
theorem repeated_difference_double_pair (low high differences : Finset ℕ)
    (horder : ∀ a ∈ low, ∀ b ∈ high, a < b)
    (hdiff : ∀ a ∈ low, ∀ b ∈ high, b - a ∈ differences)
    (hcount : differences.card < low.card * high.card) :
    ∃ b : DoublePair, b.valid low high := by
  have hcross : differences.card < (low ×ˢ high).card := by
    simpa using hcount
  obtain ⟨x, hx, y, hy, hxy, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcross
      (f := fun p : ℕ × ℕ => p.2 - p.1) (by
        intro p hp
        exact hdiff p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2)
  obtain ⟨a₁, b₁⟩ := x
  obtain ⟨a₂, b₂⟩ := y
  have hx' := Finset.mem_product.mp hx
  have hy' := Finset.mem_product.mp hy
  have ho₁ := horder a₁ hx'.1 b₁ hx'.2
  have ho₂ := horder a₂ hy'.1 b₂ hy'.2
  have ha : a₁ ≠ a₂ := by
    intro h
    subst a₂
    have : b₁ = b₂ := by omega
    subst b₂
    exact hxy rfl
  have hb : b₁ ≠ b₂ := by
    intro h
    subst b₂
    have : a₁ = a₂ := by omega
    exact ha this
  exact ⟨⟨a₁, a₂, b₁, b₂⟩, hx'.1, hy'.1, hx'.2, hy'.2, ha, hb, ho₁, ho₂, heq⟩

/-- The FC2K5 square gate supplies the strict pigeonhole inequality. -/
theorem repeated_difference_of_square_gate (low high differences : Finset ℕ) (M K : ℕ)
    (horder : ∀ a ∈ low, ∀ b ∈ high, a < b)
    (hdiff : ∀ a ∈ low, ∀ b ∈ high, b - a ∈ differences)
    (hlow : M ≤ low.card) (hhigh : M ≤ high.card)
    (hspan : differences.card ≤ K) (hgate : K < M * M) :
    ∃ b : DoublePair, b.valid low high := by
  apply repeated_difference_double_pair low high differences horder hdiff
  have hmul : M * M ≤ low.card * high.card := Nat.mul_le_mul hlow hhigh
  omega

/-- Pay for each side's actual deletions before applying the square gate. -/
theorem repeated_difference_after_deletions (low high differences removedLow removedHigh : Finset ℕ)
    (M K : ℕ) (horder : ∀ a ∈ low, ∀ b ∈ high, a < b)
    (hdiff : ∀ a ∈ low, ∀ b ∈ high, b - a ∈ differences)
    (hlow : M + removedLow.card ≤ low.card)
    (hhigh : M + removedHigh.card ≤ high.card)
    (hspan : differences.card ≤ K) (hgate : K < M * M) :
    ∃ b : DoublePair, b.valid (low \ removedLow) (high \ removedHigh) := by
  apply repeated_difference_of_square_gate _ _ differences M K
  · intro a ha b hb
    exact horder a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1
  · intro a ha b hb
    exact hdiff a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1
  · have h := Finset.card_le_card_sdiff_add_card (s := low) (t := removedLow)
    omega
  · have h := Finset.card_le_card_sdiff_add_card (s := high) (t := removedHigh)
    omega
  · exact hspan
  · exact hgate

/-- At most H+1 even integers lie in an interval of integer length 2H.
The lower endpoint need not itself be even. -/
theorem even_span_card_le (differences : Finset ℕ) (lower H : ℕ)
    (hspan : ∀ d ∈ differences, lower ≤ d ∧ d ≤ lower + 2 * H)
    (heven : ∀ d ∈ differences, d % 2 = 0) :
    differences.card ≤ H + 1 := by
  have h := Finset.card_le_card_of_injOn (s := differences) (t := Finset.range (H + 1))
    (fun d => (d - lower) / 2) (by
      intro d hd
      change (d - lower) / 2 ∈ Finset.range (H + 1)
      rw [Finset.mem_range]
      have hh := hspan d hd
      omega) (by
      intro a ha b hb hab
      change (a - lower) / 2 = (b - lower) / 2 at hab
      have h₁ := hspan a ha
      have h₂ := hspan b hb
      have he₁ := heven a ha
      have he₂ := heven b hb
      omega)
  simpa using h

/-- Shift a nonempty even set in a real interval of length 2h to an integer
interval of length 2 floor(h), starting at its least member. -/
theorem even_real_span_int_bounds (differences : Finset ℕ) (lower h : ℝ)
    (hspan : ∀ d ∈ differences, lower < (d : ℝ) ∧ (d : ℝ) ≤ lower + 2 * h)
    (heven : ∀ d ∈ differences, d % 2 = 0) (hn : differences.Nonempty) :
    ∃ least : ℕ, ∀ d ∈ differences, least ≤ d ∧ d ≤ least + 2 * ⌊h⌋₊ := by
  let least := differences.min' hn
  have hleast : least ∈ differences := Finset.min'_mem differences hn
  have hle : ∀ d ∈ differences, least ≤ d := fun d hd => Finset.min'_le differences d hd
  refine ⟨least, ?_⟩
  intro d hd
  have hdle := hle d hd
  have hreal := hspan d hd
  have hleastreal := hspan least hleast
  have hfloor := Nat.lt_floor_add_one h
  have hcast : ((d - least : ℕ) : ℝ) < 2 * ((⌊h⌋₊ : ℝ) + 1) := by
    rw [Nat.cast_sub hdle]
    linarith
  have hnat : d - least < 2 * (⌊h⌋₊ + 1) := by exact_mod_cast hcast
  have hdEven := heven d hd
  have hlEven := heven least hleast
  exact ⟨hdle, by omega⟩

/-- The source's real-width version: an interval of length 2h contains at
most floor(h)+1 even integers. No endpoint integrality is required. -/
theorem even_real_span_card_le (differences : Finset ℕ) (lower h : ℝ)
    (hspan : ∀ d ∈ differences, lower < (d : ℝ) ∧ (d : ℝ) ≤ lower + 2 * h)
    (heven : ∀ d ∈ differences, d % 2 = 0) :
    differences.card ≤ ⌊h⌋₊ + 1 := by
  by_cases hn : differences.Nonempty
  · obtain ⟨least, hbounds⟩ := even_real_span_int_bounds differences lower h hspan heven hn
    exact even_span_card_le differences least ⌊h⌋₊ hbounds heven
  · have hempty : differences = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [hempty]

/-- The manuscript's strict real square gate implies the integer
floor-width gate used by the finite pigeonhole argument. -/
theorem real_square_gate_implies_floor_gate (M : ℕ) (h : ℝ) (hwidth : 0 ≤ h)
    (hgate : h + 1 < (M : ℝ) * M) : ⌊h⌋₊ + 1 < M * M := by
  have hf := Nat.floor_le hwidth
  have hcast : ((⌊h⌋₊ + 1 : ℕ) : ℝ) < ((M * M : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hcast

/-- A bounded span of even cross-differences discharges the exact finite
pigeonhole count, without assuming any individual gap is small. -/
theorem repeated_even_difference_of_span (low high : Finset ℕ) (M lower H : ℕ)
    (horder : ∀ a ∈ low, ∀ b ∈ high, a < b)
    (hspan : ∀ a ∈ low, ∀ b ∈ high,
      lower ≤ b - a ∧ b - a ≤ lower + 2 * H)
    (heven : ∀ a ∈ low, ∀ b ∈ high, (b - a) % 2 = 0)
    (hlow : M ≤ low.card) (hhigh : M ≤ high.card) (hgate : H + 1 < M * M) :
    ∃ b : DoublePair, b.valid low high := by
  let differences := (low ×ˢ high).image (fun p : ℕ × ℕ => p.2 - p.1)
  have hd : ∀ a ∈ low, ∀ b ∈ high, b - a ∈ differences := by
    intro a ha b hb
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
  have hs : differences.card ≤ H + 1 := by
    apply even_span_card_le differences lower H
    · intro d hd'
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hd'
      exact hspan a (Finset.mem_product.mp hab).1 b (Finset.mem_product.mp hab).2
    · intro d hd'
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hd'
      exact heven a (Finset.mem_product.mp hab).1 b (Finset.mem_product.mp hab).2
  exact repeated_difference_of_square_gate low high differences M (H + 1)
    horder hd hlow hhigh hs hgate

end
end Sude
