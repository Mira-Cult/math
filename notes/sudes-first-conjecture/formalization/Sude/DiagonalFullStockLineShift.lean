import Sude.RegularFactorRF2
import Sude.DiagonalFullStockMean
namespace Sude
noncomputable section

/-- The signed conditional-expectation change from installing any disjoint
family, charged by its line incidence and the remaining-pool mean shift. -/
theorem full_stock_line_baseline_shift {n : ℕ}
    (a b : Cell n ≃ Fin (n * n)) (reserved D line : Finset (Cell n))
    (μ₀ μ₁ δ ζ : ℝ)
    (hdisj : Disjoint reserved D)
    (hfixed : ∀ z ∈ reserved, entry b z = entry a z)
    (hnear : ∀ z ∈ D, |(entry b z : ℝ) - μ₀| ≤ δ)
    (hshift : |μ₁ - μ₀| ≤ ζ) :
    |((∑ z ∈ line ∩ (reserved ∪ D), (entry b z : ℝ)) +
        ((line \ (reserved ∪ D)).card : ℝ) * μ₁) -
      ((∑ z ∈ line ∩ reserved, (entry a z : ℝ)) +
        ((line \ reserved).card : ℝ) * μ₀)| ≤
      ((line ∩ D).card : ℝ) * δ + ((line \ (reserved ∪ D)).card : ℝ) * ζ := by
  classical
  let old : ℝ := ∑ z ∈ line ∩ reserved, (entry a z : ℝ)
  let added : ℝ := ∑ z ∈ line ∩ D, (entry b z : ℝ)
  let m := (line ∩ D).card
  let k := (line \ (reserved ∪ D)).card
  have hsplit := factor_line_fixed_sum a b reserved D line hdisj hfixed
  have herr : |added - (m : ℝ) * μ₀| ≤ (m : ℝ) * δ := by
    have hp : ∀ z ∈ line ∩ D, |(entry b z : ℝ) - μ₀| ≤ δ := by
      intro z hz
      exact hnear z (Finset.mem_inter.mp hz).2
    have hsum := Finset.abs_sum_le_sum_abs (fun z => (entry b z : ℝ) - μ₀) (line ∩ D)
    have hterms : (∑ z ∈ line ∩ D, |(entry b z : ℝ) - μ₀|) ≤ ∑ _z ∈ line ∩ D, δ :=
      Finset.sum_le_sum hp
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum hterms
    dsimp [added, m]
    linarith
  have hmean : |(k : ℝ) * (μ₁ - μ₀)| ≤ (k : ℝ) * ζ := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k)]
    exact mul_le_mul_of_nonneg_left hshift (by positivity)
  have hpartition : line \ reserved = (line ∩ D) ∪ (line \ (reserved ∪ D)) := by
    ext z
    have hd : z ∈ D → z ∉ reserved := fun hz hr => Finset.disjoint_left.mp hdisj hr hz
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
    by_cases hzD : z ∈ D <;> aesop
  have hd : Disjoint (line ∩ D) (line \ (reserved ∪ D)) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact (Finset.mem_sdiff.mp hz').2 (Finset.mem_union_right _ (Finset.mem_inter.mp hz).2)
  have hcard : (line \ reserved).card = m + k := by
    rw [hpartition, Finset.card_union_of_disjoint hd]
  have hcardR : ((line \ reserved).card : ℝ) = (m : ℝ) + k := by exact_mod_cast hcard
  have hid : ((old + added) + (k : ℝ) * μ₁) - (old + ((m : ℝ) + k) * μ₀) =
      (added - (m : ℝ) * μ₀) + (k : ℝ) * (μ₁ - μ₀) := by ring
  have htri := abs_add_le (added - (m : ℝ) * μ₀) ((k : ℝ) * (μ₁ - μ₀))
  change |((∑ z ∈ line ∩ (reserved ∪ D), (entry b z : ℝ)) + (k : ℝ) * μ₁) -
    (old + ((line \ reserved).card : ℝ) * μ₀)| ≤ (m : ℝ) * δ + (k : ℝ) * ζ
  rw [hsplit, hcardR]
  change |(old + added + (k : ℝ) * μ₁) - (old + ((m : ℝ) + k) * μ₀)| ≤ _
  rw [hid]
  linarith
/-- For a supplied line meeting the installed families at most twice, the
actual post-placement conditional expectation changes by at most
`2X + kX/N`, where `k` and `N` are the actual remaining line and pool sizes. -/
theorem placed_full_stock_line_expectation_shift {n : ℕ}
    (a b : Cell n ≃ Fin (n * n)) (reserved Y Z line : Finset (Cell n))
    (T U : Finset (pool n)) (hT : T ⊆ actualUnusedPool a reserved)
    (hU : U ⊆ actualUnusedPool a reserved \ T)
    (hTc : T.card = Y.card) (hUc : U.card = Z.card)
    (hY : Y.image (entry b) = T.image Subtype.val)
    (hZ : Z.image (entry b) = U.image Subtype.val)
    (hdis : Disjoint reserved (Y ∪ Z))
    (hfixed : ∀ z ∈ reserved, entry b z = entry a z)
    (hremain : actualUnusedPool b (reserved ∪ (Y ∪ Z)) =
      (actualUnusedPool a reserved \ T) \ U)
    (hpos : 0 < (actualUnusedPool b (reserved ∪ (Y ∪ Z))).card)
    (hsum : |(∑ z ∈ Y ∪ Z, (entry b z : ℝ)) - ((Y.card + Z.card : ℕ) : ℝ) *
      centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤ (poolMaximum n : ℝ))
    (hincidence : (line ∩ (Y ∪ Z)).card ≤ 2) :
    |((∑ z ∈ line ∩ (reserved ∪ (Y ∪ Z)), (entry b z : ℝ)) +
        ((line \ (reserved ∪ (Y ∪ Z))).card : ℝ) *
          centralEntriesMean (actualUnusedPool b (reserved ∪ (Y ∪ Z))) centralPoolValue) -
      ((∑ z ∈ line ∩ reserved, (entry a z : ℝ)) +
        ((line \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
      2 * (poolMaximum n : ℝ) + ((line \ (reserved ∪ (Y ∪ Z))).card : ℝ) *
        ((poolMaximum n : ℝ) / (actualUnusedPool b (reserved ∪ (Y ∪ Z))).card) := by
  have h := placed_full_stock_mean_and_width a b reserved Y Z T U hT hU hTc hUc hY hZ hremain hpos hsum
  have hb := full_stock_line_baseline_shift a b reserved (Y ∪ Z) line
    (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)
    (centralEntriesMean (actualUnusedPool b (reserved ∪ (Y ∪ Z))) centralPoolValue)
    (poolMaximum n : ℝ) ((poolMaximum n : ℝ) / (actualUnusedPool b (reserved ∪ (Y ∪ Z))).card)
    hdis hfixed h.2 h.1
  have hcount : ((line ∩ (Y ∪ Z)).card : ℝ) ≤ 2 := by exact_mod_cast hincidence
  have hX : 0 ≤ (poolMaximum n : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hcount hX]

end
end Sude
