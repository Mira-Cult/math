import Sude.RegularFactorMatching
import Sude.LayerTranspose

/-! The numerical part of RF1's dense residual-graph cut argument.
This proves a cut lower bound from two degree-counting estimates; it does not
construct the integral factor or assert that the estimates hold for a graph. -/
namespace Sude

/-- RF1's two-case arithmetic, with omitted left and right vertex counts
`a` and `b`. The two estimates arise respectively by counting from the right
vertices in the cut and subtracting the degree of omitted left vertices. -/
theorem dense_factor_cut_bound (n a b r Δ k e : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hr : 3 * n ≤ 4 * r) (hΔ : 0 ≤ Δ)
    (hk : k ≤ r - Δ / 2) (hk0 : 0 ≤ k)
    (he0 : 0 ≤ e)
    (he₁ : (n - b) * (r - a) ≤ e)
    (he₂ : r * (n - b) - (r + Δ) * a ≤ e) :
    k * (n - a - b) ≤ e := by
  by_cases hs : n - a - b ≤ 0
  · have := mul_nonpos_of_nonneg_of_nonpos hk0 hs
    linarith
  · have hs' : 0 ≤ n - a - b := by linarith
    by_cases hb : n - r ≤ b
    · have hp := mul_nonneg ha (show 0 ≤ r - n + b by linarith)
      have hkr := mul_le_mul_of_nonneg_right (show k ≤ r by linarith) hs'
      nlinarith
    · have htwo : 0 ≤ n - a - b - 2 * a := by linarith
      have hp := mul_nonneg hΔ htwo
      have hkr := mul_le_mul_of_nonneg_right hk hs'
      nlinarith

/-- Number of actual edges from rows `A` to columns `B`. -/
def cellCutCount {n : ℕ} (E : Finset (Cell n)) (A B : Finset (Fin n)) : ℕ :=
  ∑ j ∈ B, (A.bipartiteBelow (fun i j => (i, j) ∈ E) j).card

/-- Counting the omitted rows in each column gives the first RF1 estimate. -/
theorem cell_cut_column_degree_bound {n r : ℕ} (E : Finset (Cell n))
    (A B : Finset (Fin n))
    (hcol : ∀ j, r ≤ (LayerPacking.colUsed E j).card) :
    B.card * r ≤ cellCutCount E A B + B.card * (Finset.univ \ A).card := by
  classical
  have hone : ∀ j ∈ B, r ≤ (A.bipartiteBelow (fun i j => (i, j) ∈ E) j).card +
      (Finset.univ \ A).card := by
    intro j hj
    have hc := Finset.card_le_card_sdiff_add_card (s := LayerPacking.colUsed E j) (t := Finset.univ \ A)
    have heq : LayerPacking.colUsed E j \ (Finset.univ \ A) =
        A.bipartiteBelow (fun i j => (i, j) ∈ E) j := by
      ext i
      simp [LayerPacking.colUsed, Finset.bipartiteBelow, and_comm]
    rw [heq] at hc
    exact (hcol j).trans hc
  have hs := Finset.sum_le_sum hone
  simpa [cellCutCount, Finset.sum_add_distrib, Finset.mul_sum] using hs

/-- The second RF1 estimate counts all edges at selected columns and charges
those from omitted rows against their upper degree bound. -/
theorem cell_cut_omitted_row_bound {n r Δ : ℕ} (E : Finset (Cell n))
    (A B : Finset (Fin n))
    (hcol : ∀ j, r ≤ (LayerPacking.colUsed E j).card)
    (hrow : ∀ i, (LayerPacking.rowUsed E i).card ≤ r + Δ) :
    B.card * r ≤ cellCutCount E A B + (Finset.univ \ A).card * (r + Δ) := by
  classical
  have hall : B.card * r ≤ cellCutCount E Finset.univ B := by
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ B) => hcol j)
    simpa [cellCutCount, Finset.bipartiteBelow, LayerPacking.colUsed] using hs
  have homit : cellCutCount E (Finset.univ \ A) B ≤
      (Finset.univ \ A).card * (r + Δ) := by
    unfold cellCutCount
    rw [← Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    have hone : ∀ i ∈ Finset.univ \ A,
        (B.bipartiteAbove (fun i j => (i, j) ∈ E) i).card ≤ r + Δ := by
      intro i hi
      have hsub : B.bipartiteAbove (fun i j => (i, j) ∈ E) i ⊆ LayerPacking.rowUsed E i := by
        intro j hj
        simp only [Finset.mem_bipartiteAbove] at hj
        simp [LayerPacking.rowUsed, hj.2]
      exact (Finset.card_le_card hsub).trans (hrow i)
    simpa using Finset.sum_le_sum hone
  have hsplit : cellCutCount E Finset.univ B =
      cellCutCount E A B + cellCutCount E (Finset.univ \ A) B := by
    unfold cellCutCount
    simp_rw [← Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    symm
    simpa [add_comm] using
      (Finset.sum_sdiff (s₁ := A) (s₂ := Finset.univ)
        (f := fun i => (B.bipartiteAbove (fun i j => (i, j) ∈ E) i).card)
        (Finset.subset_univ A))
  omega

/-- The actual cut inequality when the omitted row set is no larger than the
omitted column set. The opposite ordering can be handled by transposition. -/
theorem dense_factor_cut_ordered {n r Δ k : ℕ} (E : Finset (Cell n))
    (A B : Finset (Fin n))
    (hcol : ∀ j, r ≤ (LayerPacking.colUsed E j).card)
    (hrow : ∀ i, (LayerPacking.rowUsed E i).card ≤ r + Δ)
    (hdense : 3 * n ≤ 4 * r) (hk : 2 * k + Δ ≤ 2 * r)
    (horder : (Finset.univ \ A).card ≤ (Finset.univ \ B).card) :
    k * (A.card + B.card - n) ≤ cellCutCount E A B := by
  classical
  let a := (Finset.univ \ A).card
  let b := (Finset.univ \ B).card
  have hA : a + A.card = n := by
    simpa [a] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  have hB : b + B.card = n := by
    simpa [b] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
  have ha : (a : ℝ) + A.card = n := by exact_mod_cast hA
  have hb : (b : ℝ) + B.card = n := by exact_mod_cast hB
  have hden : (3 : ℝ) * n ≤ 4 * r := by exact_mod_cast hdense
  have hkn : (2 : ℝ) * k + Δ ≤ 2 * r := by exact_mod_cast hk
  have hord : (a : ℝ) ≤ b := by exact_mod_cast horder
  have hc₁ : (B.card : ℝ) * r ≤ cellCutCount E A B + B.card * a := by
    exact_mod_cast cell_cut_column_degree_bound E A B hcol
  have hc₂ : (B.card : ℝ) * r ≤ cellCutCount E A B + a * (r + Δ) := by
    exact_mod_cast cell_cut_omitted_row_bound E A B hcol hrow
  have hbound := dense_factor_cut_bound (n : ℝ) a b r Δ k (cellCutCount E A B)
    (by positivity) hord hden (by positivity) (by linarith [hkn]) (by positivity)
    (by positivity) (by nlinarith [hc₁]) (by nlinarith [hc₂])
  by_cases hsum : n ≤ A.card + B.card
  · have hreal : (k : ℝ) * ((A.card + B.card - n : ℕ) : ℝ) ≤ cellCutCount E A B := by
      rw [Nat.cast_sub hsum]
      push_cast
      nlinarith [hbound]
    exact_mod_cast hreal
  · have hz : A.card + B.card - n = 0 := by omega
    simp [hz]

/-- Transposition exchanges both sides of an actual cut. -/
theorem cellCutCount_transpose {n : ℕ} (E : Finset (Cell n)) (A B : Finset (Fin n)) :
    cellCutCount (LayerPacking.transposeCells E) B A = cellCutCount E A B := by
  classical
  unfold cellCutCount
  rw [← Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ext i
  simp [Finset.bipartiteAbove, Finset.bipartiteBelow, LayerPacking.transposeCells,
    Prod.ext_iff]

/-- RF1's cut inequality for every actual row/column cut. Both degree bounds
are stated explicitly, and the transpose handles the other ordering. -/
theorem dense_factor_all_cuts {n r Δ k : ℕ} (E : Finset (Cell n))
    (hrowlo : ∀ i, r ≤ (LayerPacking.rowUsed E i).card)
    (hrowhi : ∀ i, (LayerPacking.rowUsed E i).card ≤ r + Δ)
    (hcollo : ∀ j, r ≤ (LayerPacking.colUsed E j).card)
    (hcolhi : ∀ j, (LayerPacking.colUsed E j).card ≤ r + Δ)
    (hdense : 3 * n ≤ 4 * r) (hk : 2 * k + Δ ≤ 2 * r) :
    ∀ A B : Finset (Fin n), k * (A.card + B.card - n) ≤ cellCutCount E A B := by
  intro A B
  by_cases hord : (Finset.univ \ A).card ≤ (Finset.univ \ B).card
  · exact dense_factor_cut_ordered E A B hcollo hrowhi hdense hk hord
  · have hord' : (Finset.univ \ B).card ≤ (Finset.univ \ A).card := by omega
    have h := dense_factor_cut_ordered (LayerPacking.transposeCells E) B A
      (by simpa using hrowlo) (by simpa using hcolhi) hdense hk hord'
    simpa [cellCutCount_transpose, Nat.add_comm] using h

/-- The source choice `r - ceil(Δ/2)` satisfies the verified cut criterion,
provided the natural-number subtraction has not underflowed. -/
theorem dense_factor_source_cuts {n r Δ : ℕ} (E : Finset (Cell n))
    (hrowlo : ∀ i, r ≤ (LayerPacking.rowUsed E i).card)
    (hrowhi : ∀ i, (LayerPacking.rowUsed E i).card ≤ r + Δ)
    (hcollo : ∀ j, r ≤ (LayerPacking.colUsed E j).card)
    (hcolhi : ∀ j, (LayerPacking.colUsed E j).card ≤ r + Δ)
    (hdense : 3 * n ≤ 4 * r) (hceil : (Δ + 1) / 2 ≤ r) :
    ∀ A B : Finset (Fin n),
      (r - (Δ + 1) / 2) * (A.card + B.card - n) ≤ cellCutCount E A B := by
  apply dense_factor_all_cuts E hrowlo hrowhi hcollo hcolhi hdense
  omega

end Sude
