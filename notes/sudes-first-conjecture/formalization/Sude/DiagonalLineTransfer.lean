import Sude.CentralPairDiagonal
import Sude.RegularFactorRF2

/-! Transfer a completion error across actual diagonal preassignments. -/
namespace Sude
noncomputable section

/-- Newly reserved diagonal cells and the change of unused mean add at most
their explicit line and mean-shift budgets to an existing completion error. -/
theorem diagonal_preassignment_line_transfer {n : ℕ}
    (a b : Cell n ≃ Fin (n * n)) (reserved line : Finset (Cell n))
    (s μ₀ μ₁ δ ζ E : ℝ) (hδ : 0 ≤ δ) (hζ : 0 ≤ ζ)
    (hfixed : ∀ z ∈ reserved, entry b z = entry a z)
    (hcentral : ∀ z ∈ unreservedDiagonalCells reserved, |(entry b z : ℝ) - μ₀| ≤ δ)
    (hshift : |μ₁ - μ₀| ≤ ζ)
    (hline : line.card ≤ n) (hdiag : (line ∩ unreservedDiagonalCells reserved).card ≤ 2)
    (hafter : |s - ((∑ z ∈ line ∩ (reserved ∪ unreservedDiagonalCells reserved), (entry b z : ℝ)) +
      ((line \ (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) * μ₁)| < E) :
    |s - ((∑ z ∈ line ∩ reserved, (entry a z : ℝ)) +
      ((line \ reserved).card : ℝ) * μ₀)| < E + 2 * δ + n * ζ := by
  classical
  let D := unreservedDiagonalCells reserved
  let old : ℝ := ∑ z ∈ line ∩ reserved, (entry a z : ℝ)
  let added : ℝ := ∑ z ∈ line ∩ D, (entry b z : ℝ)
  let m := (line ∩ D).card
  let k := (line \ (reserved ∪ D)).card
  have hdisj : Disjoint reserved D := by
    apply Finset.disjoint_left.mpr
    intro z hz hd
    exact (Finset.mem_sdiff.mp hd).2 hz
  have hsplit := factor_line_fixed_sum a b reserved D line hdisj hfixed
  have hfactor : |(s - old - added) - (k : ℝ) * μ₁| < E := by
    rw [hsplit] at hafter
    convert hafter using 1; dsimp [old, added, k, D]; ring_nf
  have hdiagerr : |added - (m : ℝ) * μ₀| ≤ 2 * δ := by
    have hp : ∀ z ∈ line ∩ D, |(entry b z : ℝ) - μ₀| ≤ δ := by
      intro z hz
      exact hcentral z (Finset.mem_inter.mp hz).2
    have hsum := Finset.abs_sum_le_sum_abs (fun z => (entry b z : ℝ) - μ₀) (line ∩ D)
    have hterms : (∑ z ∈ line ∩ D, |(entry b z : ℝ) - μ₀|) ≤ ∑ _z ∈ line ∩ D, δ :=
      Finset.sum_le_sum hp
    have hcount : (m : ℝ) ≤ 2 := by exact_mod_cast hdiag
    have hmul := mul_le_mul_of_nonneg_right hcount hδ
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum hterms
    dsimp [added, m]
    linarith
  have hk : (k : ℝ) ≤ n := by
    have hk' : k ≤ line.card := Finset.card_le_card Finset.sdiff_subset
    have hk'' : k ≤ n := hk'.trans hline
    exact_mod_cast hk''
  have hmeanerr : |(k : ℝ) * (μ₁ - μ₀)| ≤ n * ζ := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k)]
    calc
      _ ≤ (k : ℝ) * ζ := mul_le_mul_of_nonneg_left hshift (by positivity)
      _ ≤ (n : ℝ) * ζ := mul_le_mul_of_nonneg_right hk hζ
  have hpartition : line \ reserved = (line ∩ D) ∪ (line \ (reserved ∪ D)) := by
    ext z
    have hd : z ∈ D → z ∉ reserved := fun hz => (Finset.mem_sdiff.mp hz).2
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
    by_cases hzD : z ∈ D <;> aesop
  have hdisjoint : Disjoint (line ∩ D) (line \ (reserved ∪ D)) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact (Finset.mem_sdiff.mp hz').2 (Finset.mem_union_right _ (Finset.mem_inter.mp hz).2)
  have hcard : (line \ reserved).card = m + k := by
    rw [hpartition, Finset.card_union_of_disjoint hdisjoint]
  have hcardR : ((line \ reserved).card : ℝ) = (m : ℝ) + k := by exact_mod_cast hcard
  rw [hcardR]
  have ht₁ := abs_add_le ((s - old - added) - (k : ℝ) * μ₁)
    ((added - (m : ℝ) * μ₀) + (k : ℝ) * (μ₁ - μ₀))
  have ht₂ := abs_add_le (added - (m : ℝ) * μ₀) ((k : ℝ) * (μ₁ - μ₀))
  have heq : s - (old + ((m : ℝ) + k) * μ₀) =
      ((s - old - added) - (k : ℝ) * μ₁) +
      ((added - (m : ℝ) * μ₀) + (k : ℝ) * (μ₁ - μ₀)) := by ring
  change |s - (old + ((m : ℝ) + k) * μ₀)| < _
  rw [heq]
  linarith

theorem rowCells_card_exact {n : ℕ} (r : Fin n) : (rowCells r).card = n := by
  classical
  unfold rowCells
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j h
    exact congrArg Prod.snd h

theorem columnCells_card_exact {n : ℕ} (c : Fin n) : (columnCells c).card = n := by
  classical
  unfold columnCells
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j h
    exact congrArg Prod.fst h

/-- The transfer bound applies simultaneously to every actual row and
column, including the coincident diagonal cell in odd orders. -/
theorem diagonal_preassignment_rows_columns_transfer {n : ℕ}
    (a b c : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (μ₀ μ₁ δ ζ E : ℝ) (hδ : 0 ≤ δ) (hζ : 0 ≤ ζ)
    (hfixed : ∀ z ∈ reserved, entry b z = entry a z)
    (hcentral : ∀ z ∈ unreservedDiagonalCells reserved, |(entry b z : ℝ) - μ₀| ≤ δ)
    (hshift : |μ₁ - μ₀| ≤ ζ)
    (hrows : ∀ i, |(rowSum c i : ℝ) -
      ((∑ z ∈ rowCells i ∩ (reserved ∪ unreservedDiagonalCells reserved), (entry b z : ℝ)) +
        ((rowCells i \ (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) * μ₁)| < E)
    (hcols : ∀ i, |(columnSum c i : ℝ) -
      ((∑ z ∈ columnCells i ∩ (reserved ∪ unreservedDiagonalCells reserved), (entry b z : ℝ)) +
        ((columnCells i \ (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) * μ₁)| < E) :
    (∀ i, |(rowSum c i : ℝ) -
      ((∑ z ∈ rowCells i ∩ reserved, (entry a z : ℝ)) +
        ((rowCells i \ reserved).card : ℝ) * μ₀)| < E + 2 * δ + n * ζ) ∧
    (∀ i, |(columnSum c i : ℝ) -
      ((∑ z ∈ columnCells i ∩ reserved, (entry a z : ℝ)) +
        ((columnCells i \ reserved).card : ℝ) * μ₀)| < E + 2 * δ + n * ζ) := by
  constructor
  · intro i
    exact diagonal_preassignment_line_transfer a b reserved (rowCells i) (rowSum c i) μ₀ μ₁ δ ζ E
      hδ hζ hfixed hcentral hshift (by simp [rowCells_card_exact])
      (row_unreserved_diagonal_card_le_two reserved i) (hrows i)
  · intro i
    exact diagonal_preassignment_line_transfer a b reserved (columnCells i) (columnSum c i) μ₀ μ₁ δ ζ E
      hδ hζ hfixed hcentral hshift (by simp [columnCells_card_exact])
      (column_unreserved_diagonal_card_le_two reserved i) (hcols i)

/-- The CC diagonal windows and mean update contribute at most `5η/2`
plus the exact remaining-pool mean-shift term to each row and column. -/
theorem central_diagonal_rows_columns_transfer {n : ℕ}
    (a b c : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (η E : ℝ) (hη : 0 ≤ η)
    (hfixed : ∀ z ∈ reserved, entry b z = entry a z)
    (hcentral : ∀ z ∈ unreservedDiagonalCells reserved,
      |(entry b z : ℝ) - (Lucas.poolTotal n : ℝ) / (n * n : ℕ)| ≤ η)
    (hmean0 : |centralEntriesMean (actualUnusedPool a reserved) centralPoolValue -
      (Lucas.poolTotal n : ℝ) / (n * n : ℕ)| ≤ η / 4)
    (hshift : |centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
      centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
        3 * η / (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card)
    (hrows : ∀ i, |(rowSum c i : ℝ) -
      ((∑ z ∈ rowCells i ∩ (reserved ∪ unreservedDiagonalCells reserved), (entry b z : ℝ)) +
        ((rowCells i \ (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) *
          centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue)| < E)
    (hcols : ∀ i, |(columnSum c i : ℝ) -
      ((∑ z ∈ columnCells i ∩ (reserved ∪ unreservedDiagonalCells reserved), (entry b z : ℝ)) +
        ((columnCells i \ (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) *
          centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue)| < E) :
    (∀ i, |(rowSum c i : ℝ) -
      ((∑ z ∈ rowCells i ∩ reserved, (entry a z : ℝ)) +
        ((rowCells i \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          E + (5 / 2 : ℝ) * η + (n : ℝ) *
            (3 * η / (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card)) ∧
    (∀ i, |(columnSum c i : ℝ) -
      ((∑ z ∈ columnCells i ∩ reserved, (entry a z : ℝ)) +
        ((columnCells i \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          E + (5 / 2 : ℝ) * η + (n : ℝ) *
            (3 * η / (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card)) := by
  let μ₀ := centralEntriesMean (actualUnusedPool a reserved) centralPoolValue
  let μ₁ := centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue
  let m : ℝ := (Lucas.poolTotal n : ℝ) / (n * n : ℕ)
  let ζ : ℝ := 3 * η / (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card
  have hζ : 0 ≤ ζ := by dsimp [ζ]; positivity
  have hnear : ∀ z ∈ unreservedDiagonalCells reserved, |(entry b z : ℝ) - μ₀| ≤ (5 / 4 : ℝ) * η := by
    intro z hz
    have ht := abs_sub_le (entry b z : ℝ) m μ₀
    have hm : |m - μ₀| = |μ₀ - m| := abs_sub_comm m μ₀
    rw [hm] at ht
    have hc := hcentral z hz
    linarith
  have h := diagonal_preassignment_rows_columns_transfer a b c reserved μ₀ μ₁ ((5 / 4 : ℝ) * η) ζ E
    (by positivity) hζ hfixed hnear hshift hrows hcols
  have heq : E + 2 * ((5 / 4 : ℝ) * η) + (n : ℝ) * ζ =
      E + (5 / 2 : ℝ) * η + (n : ℝ) * ζ := by ring
  simpa only [heq] using h

end
end Sude
