import Sude.DiagonalFullStockCenterBatches
import Sude.RegularFactorRF2
import Sude.CentralDiagonalGeometry

namespace Sude
noncomputable section

/-- The second batch has deviation at most one full width relative to the
original mean, accounting for the signed first-batch mean shift. -/
theorem full_stock_second_batch_original_mean {α : Type*} [DecidableEq α]
    (stock T U : Finset α) (value : α → ℝ) (W : ℝ)
    (hT : T ⊆ stock) (hU : U ⊆ stock \ T) (hpos : 0 < (stock \ T).card)
    (hfirst : |(∑ x ∈ T, value x) - (T.card : ℝ) * centralEntriesMean stock value| ≤ W / 2)
    (hsecond : |(∑ x ∈ U, value x) - (U.card : ℝ) * centralEntriesMean (stock \ T) value| ≤ W / 2) :
    |(∑ x ∈ U, value x) - (U.card : ℝ) * centralEntriesMean stock value| ≤ W := by
  let E := (∑ x ∈ T, value x) - (T.card : ℝ) * centralEntriesMean stock value
  let F := (∑ x ∈ U, value x) - (U.card : ℝ) * centralEntriesMean (stock \ T) value
  let Q : ℝ := (U.card : ℝ) / (stock \ T).card
  have hm := central_entries_actual_mean_update stock T value hT hpos
  have hid : (∑ x ∈ U, value x) - (U.card : ℝ) * centralEntriesMean stock value = F - Q * E := by
    dsimp [F,Q,E]
    rw [hm]
    ring
  have hden : (0 : ℝ) < (stock \ T).card := by exact_mod_cast hpos
  have hqle : (U.card : ℝ) ≤ (stock \ T).card := by exact_mod_cast Finset.card_le_card hU
  have hQ : 0 ≤ Q ∧ Q ≤ 1 := by
    constructor
    · dsimp [Q]; positivity
    · exact (div_le_one hden).2 hqle
  have hF : |F| ≤ W/2 := hsecond
  have hE : |E| ≤ W/2 := hfirst
  have hweighted : |Q*E| ≤ W/2 := by
    rw [abs_mul, abs_of_nonneg hQ.1]
    have h := mul_le_mul hQ.2 hE (abs_nonneg E) (by norm_num : (0:ℝ) ≤ 1)
    linarith
  rw [hid]
  have htri := abs_sub F (Q*E)
  linarith

/-- Transfer a selected batch discrepancy to a line whose remaining cells
are exactly the batch cells. -/
theorem full_stock_complete_line_from_batch {n : ℕ}
    (a b : Cell n ≃ Fin (n*n)) (reserved D line : Finset (Cell n)) (μ δ : ℝ)
    (hD : line \ reserved = D) (hdis : Disjoint reserved D)
    (hfixed : ∀ z ∈ reserved, entry b z = entry a z)
    (herr : |(∑ z ∈ D, (entry b z : ℝ)) - (D.card : ℝ) * μ| ≤ δ) :
    |(∑ z ∈ line, (entry b z : ℝ)) -
      ((∑ z ∈ line ∩ reserved, (entry a z : ℝ)) + ((line \ reserved).card : ℝ)*μ)| ≤ δ := by
  have hsplit := factor_line_fixed_sum a b reserved D line hdis hfixed
  have hunion : line ∩ (reserved ∪ D) = line := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_union]
    have hd : z ∈ line → z ∉ reserved → z ∈ D := by
      intro hl hr
      rw [← hD]
      exact Finset.mem_sdiff.mpr ⟨hl, hr⟩
    tauto
  have hsub : D ⊆ line := by rw [← hD]; exact Finset.sdiff_subset
  have hinter : line ∩ D = D := Finset.inter_eq_right.mpr hsub
  rw [hunion, hinter] at hsplit
  rw [hsplit, hD]
  convert herr using 1 <;> ring_nf
end
end Sude
namespace Sude
noncomputable section

/-- Full-stock diagonal placement bounds both actual diagonal sums on the
same square relative to the original conditional expectations. -/
theorem odd_full_stock_actual_diagonal_bounds {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (reserved : Finset (Cell n)) (hn : 0 < n) (hodd : Odd n)
    (hcenter : centralCell n hn ∉ reserved)
    (hroom : 1 + (centralFreeMain hn reserved).card + (centralFreeAnti hn reserved).card <
      (actualUnusedPool a reserved).card) :
    ∃ b : Cell n ≃ Fin (n*n), (∀ z ∈ reserved, entry b z = entry a z) ∧
      |(mainSum b : ℝ) - ((∑ z ∈ mainCells n ∩ reserved, (entry a z : ℝ)) +
        ((mainCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (poolMaximum n : ℝ) ∧
      |(antiSum b : ℝ) - ((∑ z ∈ antiCells n ∩ reserved, (entry a z : ℝ)) +
        ((antiCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (3/2 : ℝ) * poolMaximum n := by
  classical
  let center := centralCell n hn
  let Y := centralFreeMain hn reserved
  let Z := centralFreeAnti hn reserved
  let R := reserved ∪ {center}
  obtain ⟨_, _, _, _, hYR, hZR, hXY, hXZ, hYZ, _, _⟩ :=
    central_free_diagonal_geometry hn hodd reserved hcenter
  have hYc : center ∉ Y := by simpa [center, Y] using hXY
  have hZc : center ∉ Z := by simpa [center, Z] using hXZ
  obtain ⟨b₀, b, T, U, hfixed₀, hexpect, hT, hU, hTc, hUc, hY, hZ,
    hfixed, hremain, hpos, hfirst, hsecond, _⟩ :=
    actual_center_and_two_full_stock_batches a reserved Y Z center hcenter hYR hZR hYZ hYc hZc hroom
  let stock := actualUnusedPool b₀ R
  have hposT : 0 < (stock \ T).card := by
    have hsub : (stock \ T) \ U ⊆ stock \ T := Finset.sdiff_subset
    have hcard := Finset.card_le_card hsub
    have hleft : 0 < ((stock \ T) \ U).card := by rw [← hremain]; exact hpos
    omega
  have hsumY := finite_population_sum b Y T hY
  have hsumZ := finite_population_sum b Z U hZ
  have hfirst' : |(∑ x ∈ T, centralPoolValue x) - (T.card : ℝ) * centralEntriesMean stock centralPoolValue| ≤
      (poolMaximum n : ℝ) / 2 := by simpa [stock, R, ← hTc, hsumY] using hfirst
  have hsecond' : |(∑ x ∈ U, centralPoolValue x) - (U.card : ℝ) * centralEntriesMean (stock \ T) centralPoolValue| ≤
      (poolMaximum n : ℝ) / 2 := by simpa [stock, R, ← hUc, hsumZ] using hsecond
  have hzbound := full_stock_second_batch_original_mean stock T U centralPoolValue (poolMaximum n) hT hU hposT hfirst' hsecond'
  have hzphys : |(∑ z ∈ Z, (entry b z : ℝ)) - (Z.card : ℝ) * centralEntriesMean stock centralPoolValue| ≤
      (poolMaximum n : ℝ) := by simpa [hsumZ, ← hUc] using hzbound
  have hmainD : mainCells n \ R = Y := by ext z; simp [R, Y, center, centralFreeMain, Finset.mem_sdiff, and_assoc, and_comm]
  have hantiD : antiCells n \ R = Z := by ext z; simp [R, Z, center, centralFreeAnti, Finset.mem_sdiff, and_assoc, and_comm]
  have hdisY : Disjoint R Y := (Finset.disjoint_union_right.mpr ⟨hYR, by simpa using hYc⟩).symm
  have hdisZ : Disjoint R Z := (Finset.disjoint_union_right.mpr ⟨hZR, by simpa using hZc⟩).symm
  have hm := full_stock_complete_line_from_batch b₀ b R Y (mainCells n) (centralEntriesMean stock centralPoolValue)
    ((poolMaximum n : ℝ)/2) hmainD hdisY hfixed hfirst
  have ha := full_stock_complete_line_from_batch b₀ b R Z (antiCells n) (centralEntriesMean stock centralPoolValue)
    (poolMaximum n) hantiD hdisZ hfixed hzphys
  have hmcenter := hexpect (mainCells n)
  have hacenter := hexpect (antiCells n)
  rw [← mainSum_real_cells] at hm
  rw [← antiSum_real_cells] at ha
  have hmt := abs_sub_le (mainSum b : ℝ)
    ((∑ z ∈ mainCells n ∩ R, (entry b₀ z : ℝ)) + ((mainCells n \ R).card : ℝ) * centralEntriesMean stock centralPoolValue)
    ((∑ z ∈ mainCells n ∩ reserved, (entry a z : ℝ)) + ((mainCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)
  have hat := abs_sub_le (antiSum b : ℝ)
    ((∑ z ∈ antiCells n ∩ R, (entry b₀ z : ℝ)) + ((antiCells n \ R).card : ℝ) * centralEntriesMean stock centralPoolValue)
    ((∑ z ∈ antiCells n ∩ reserved, (entry a z : ℝ)) + ((antiCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)
  refine ⟨b, ?_, ?_, ?_⟩
  · intro z hz; exact (hfixed z (Finset.mem_union_left _ hz)).trans (hfixed₀ z hz)
  · change |(mainSum b : ℝ) - _| ≤ _ at hm
    change |_ - _| ≤ _ at hmcenter
    linarith
  · change |(antiSum b : ℝ) - _| ≤ _ at ha
    change |_ - _| ≤ _ at hacenter
    linarith
end
end Sude
