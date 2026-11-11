import Sude.FWSpareRectangleLineBound

/-! Active rectangle stage means and spare entries are alternative local
contributions on each physical line. This is separate from the global spare
term already present in the full-reservation cancellation identity. -/
namespace Sude
noncomputable section

/-- Disjoint alternatives, each of cardinality at most two, have a combined
absolute sum bounded by twice the supplied pointwise bound. -/
theorem exclusive_two_cell_sums_bound {α : Type*} [DecidableEq α]
    (A S : Finset α) (f g : α → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hA : A.card ≤ 2) (hS : S.card ≤ 2)
    (hsep : A = ∅ ∨ S = ∅)
    (hf : ∀ x ∈ A, |f x| ≤ B) (hg : ∀ x ∈ S, |g x| ≤ B) :
    |(∑ x ∈ A, f x) + (∑ x ∈ S, g x)| ≤ 2 * B := by
  have hsum (T : Finset α) (h : α → ℝ) (hc : T.card ≤ 2) (hb : ∀ x ∈ T, |h x| ≤ B) :
      |∑ x ∈ T, h x| ≤ 2 * B := by
    calc
      _ ≤ ∑ x ∈ T, |h x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ T, B := Finset.sum_le_sum hb
      _ = (T.card : ℝ) * B := by simp
      _ ≤ 2 * B := by gcongr; exact_mod_cast hc
  rcases hsep with ha | hs
  · simp only [ha, Finset.sum_empty, zero_add]
    exact hsum S g hS hg
  · simp only [hs, Finset.sum_empty, add_zero]
    exact hsum A f hA hf

/-- On every row or column the active rectangle cells and spare rectangle
cells are mutually exclusive. The supplied `owner` must be connected separately
to the actual stage labels when using this estimate in a stage-mean identity. -/
theorem fw_active_spare_rectangle_means_bound {n P : ℕ} (hP : P ≤ 238)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    {I : Type*} (owner : Cell n → I) (stageMean : I → ℝ)
    (a : Cell n ≃ Fin (n*n)) (X μ : ℝ) (hX : 0 ≤ X)
    (hstage : ∀ j, |stageMean j - μ| ≤ (257 / 500 : ℝ) * X)
    (hvalues : ∀ c : Cell n, 0 ≤ (entry a c : ℝ) ∧ (entry a c : ℝ) ≤ X)
    (hlo : (243 / 500 : ℝ) * X ≤ μ) (hhi : μ ≤ (123 / 250 : ℝ) * X) :
    let active := activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
    let spare := packedRectangleSupport hs choice \ active
    (∀ r : Fin n,
      (LayerPacking.rowUsed active r = ∅ ∨ LayerPacking.rowUsed spare r = ∅) ∧
      |(∑ j ∈ LayerPacking.rowUsed active r, (stageMean (owner (r,j)) - μ)) +
       (∑ j ∈ LayerPacking.rowUsed spare r, ((entry a (r,j) : ℝ) - μ))| ≤ (257 / 250 : ℝ) * X) ∧
    (∀ j : Fin n,
      (LayerPacking.colUsed active j = ∅ ∨ LayerPacking.colUsed spare j = ∅) ∧
      |(∑ r ∈ LayerPacking.colUsed active j, (stageMean (owner (r,j)) - μ)) +
       (∑ r ∈ LayerPacking.colUsed spare j, ((entry a (r,j) : ℝ) - μ))| ≤ (257 / 250 : ℝ) * X) := by
  classical
  dsimp only
  let active := activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
  let spare := packedRectangleSupport hs choice \ active
  have hsep := fw_spare_rectangle_line_separation hP hs choice
  have hsp : spare = activeRectangleSupport hs choice (fwSpareRectangleLabels n P hP) := hsep.2.2.2
  have hcell (c : Cell n) : |(entry a c : ℝ) - μ| ≤ (257 / 500 : ℝ) * X := by
    rcases hvalues c with ⟨hc₀, hc₁⟩
    apply abs_le.mpr
    constructor <;> linarith
  have hbound : 0 ≤ (257 / 500 : ℝ) * X := by positivity
  constructor
  · intro r
    have hA : (LayerPacking.rowUsed active r).card ≤ 2 := by
      dsimp [active]
      rcases active_rectangle_row_count hs choice (fwActiveRectangleLabels n P hP) r with h | h <;> omega
    have hS : (LayerPacking.rowUsed spare r).card ≤ 2 := by
      rw [hsp]
      rcases hsep.2.1 r with h | h <;> omega
    have hdisj : LayerPacking.rowUsed active r = ∅ ∨ LayerPacking.rowUsed spare r = ∅ := by
      by_cases ha : LayerPacking.rowUsed active r = ∅
      · exact Or.inl ha
      · right
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr ha
        have hk' : (r,k) ∈ active := by simpa [LayerPacking.rowUsed] using hk
        have hj' : (r,j) ∈ activeRectangleSupport hs choice (fwSpareRectangleLabels n P hP) := by
          simpa [LayerPacking.rowUsed, hsp] using hj
        exact (hsep.1 (r,k) hk' (r,j) hj').1 rfl
    refine ⟨hdisj, ?_⟩
    have hh := exclusive_two_cell_sums_bound (LayerPacking.rowUsed active r) (LayerPacking.rowUsed spare r)
      (fun j => stageMean (owner (r,j)) - μ) (fun j => (entry a (r,j) : ℝ) - μ)
      ((257 / 500 : ℝ) * X) hbound hA hS hdisj (fun j _ => hstage _) (fun j _ => hcell _)
    nlinarith
  · intro j
    have hA : (LayerPacking.colUsed active j).card ≤ 2 := by
      dsimp [active]
      rcases active_rectangle_column_count hs choice (fwActiveRectangleLabels n P hP) j with h | h <;> omega
    have hS : (LayerPacking.colUsed spare j).card ≤ 2 := by
      rw [hsp]
      rcases hsep.2.2.1 j with h | h <;> omega
    have hdisj : LayerPacking.colUsed active j = ∅ ∨ LayerPacking.colUsed spare j = ∅ := by
      by_cases ha : LayerPacking.colUsed active j = ∅
      · exact Or.inl ha
      · right
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro r hr
        obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr ha
        have hk' : (k,j) ∈ active := by simpa [LayerPacking.colUsed] using hk
        have hr' : (r,j) ∈ activeRectangleSupport hs choice (fwSpareRectangleLabels n P hP) := by
          simpa [LayerPacking.colUsed, hsp] using hr
        exact (hsep.1 (k,j) hk' (r,j) hr').2 rfl
    refine ⟨hdisj, ?_⟩
    have hh := exclusive_two_cell_sums_bound (LayerPacking.colUsed active j) (LayerPacking.colUsed spare j)
      (fun r => stageMean (owner (r,j)) - μ) (fun r => (entry a (r,j) : ℝ) - μ)
      ((257 / 500 : ℝ) * X) hbound hA hS hdisj (fun r _ => hstage _) (fun r _ => hcell _)
    nlinarith

end
end Sude
