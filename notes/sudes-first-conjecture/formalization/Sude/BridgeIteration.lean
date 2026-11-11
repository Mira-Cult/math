import Sude.FC2KBridge

/-! Termination of FC2K's real-valued bridge-radius recurrence. This does
not assert that the numerical stock gates hold at any stage. -/
namespace Sude
noncomputable section

def bridgeNext (X R : ℝ) : ℝ :=
  if R < X then R + bridgeGapLower X R else R

def bridgeIteration (X R₀ : ℝ) : ℕ → ℝ
  | 0 => R₀
  | j + 1 => bridgeNext X (bridgeIteration X R₀ j)

theorem bridgeGapLower_mono (X R S : ℝ) (h : R ≤ S) :
    bridgeGapLower X R ≤ bridgeGapLower X S := by
  have hs : bridgeSpan X R ≤ bridgeSpan X S := min_le_min h le_rfl
  simp only [bridgeGapLower, bridgeWidth]
  linarith

theorem bridgeNext_ge (X R : ℝ) (hX : 0 < X) (hR : 0 < R) :
    R ≤ bridgeNext X R := by
  unfold bridgeNext
  split_ifs with h
  · have hg := (bridge_window_geometry X R hX hR).2.1
    linarith
  · exact le_rfl

theorem bridgeIteration_pos (X R₀ : ℝ) (hX : 0 < X) (hR : 0 < R₀) (j : ℕ) :
    0 < bridgeIteration X R₀ j := by
  induction j with
  | zero => exact hR
  | succ j ih =>
    change 0 < bridgeNext X (bridgeIteration X R₀ j)
    exact lt_of_lt_of_le ih (bridgeNext_ge X _ hX ih)

theorem bridgeIteration_mono (X R₀ : ℝ) (hX : 0 < X) (hR : 0 < R₀) :
    Monotone (bridgeIteration X R₀) := by
  apply monotone_nat_of_le_succ
  intro j
  exact bridgeNext_ge X _ hX (bridgeIteration_pos X R₀ hX hR j)

/-- Before stopping, every stage advances by at least the positive first
increment; this is a uniform bound, not a sampled endpoint calculation. -/
theorem bridgeIteration_below_lower_bound (X R₀ : ℝ) (hX : 0 < X) (hR : 0 < R₀)
    (j : ℕ) (hbelow : bridgeIteration X R₀ j < X) :
    R₀ + j * bridgeGapLower X R₀ ≤ bridgeIteration X R₀ j := by
  induction j with
  | zero => simp [bridgeIteration]
  | succ j ih =>
    have hpos := bridgeIteration_pos X R₀ hX hR j
    have hstep := bridgeNext_ge X (bridgeIteration X R₀ j) hX hpos
    have hprev : bridgeIteration X R₀ j < X := by
      change bridgeNext X (bridgeIteration X R₀ j) < X at hbelow
      linarith
    have hold := ih hprev
    have hinit : R₀ ≤ bridgeIteration X R₀ j := by
      have hm := bridgeIteration_mono X R₀ hX hR (Nat.zero_le j)
      simpa [bridgeIteration] using hm
    have hinc := bridgeGapLower_mono X R₀ (bridgeIteration X R₀ j) hinit
    change R₀ + ((j + 1 : ℕ) : ℝ) * bridgeGapLower X R₀ ≤
      bridgeNext X (bridgeIteration X R₀ j)
    rw [bridgeNext, if_pos hprev]
    push_cast
    nlinarith

/-- The exact stopping recurrence reaches X in finitely many stages; the
least such J witnesses all preceding radii below X. -/
theorem bridgeIteration_terminates (X R₀ : ℝ) (hX : 0 < X) (hR : 0 < R₀) :
    ∃ J : ℕ, X ≤ bridgeIteration X R₀ J ∧
      ∀ j < J, bridgeIteration X R₀ j < X := by
  have hdelta : 0 < bridgeGapLower X R₀ := (bridge_window_geometry X R₀ hX hR).2.1
  obtain ⟨j, hj⟩ := exists_nat_gt (X / bridgeGapLower X R₀)
  have hlarge : X < (j : ℝ) * bridgeGapLower X R₀ := (div_lt_iff₀ hdelta).mp hj
  have hex : ∃ J : ℕ, X ≤ bridgeIteration X R₀ J := by
    refine ⟨j, ?_⟩
    by_contra h
    have hbelow : bridgeIteration X R₀ j < X := lt_of_not_ge h
    have hlower := bridgeIteration_below_lower_bound X R₀ hX hR j hbelow
    linarith
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro i hi
  exact lt_of_not_ge (Nat.find_min hex hi)

/-- A sequence of fresh, even bridge gaps satisfying the source bounds
preserves the entire integer subset-sum grid through every stage. Its actual
coverage remains at least the recursively computed real lower bound. -/
theorem bridgeIteration_preserves_grids (X R₀ : ℝ) (initial : Finset ℕ)
    (gap : ℕ → ℕ) (radius J : ℕ)
    (hgrid : CompleteEvenGrid initial gap radius) (hradius : 2 ∣ radius)
    (hcoverage : R₀ ≤ (radius : ℝ))
    (hbelow : ∀ j < J, bridgeIteration X R₀ j < X)
    (hfresh : ∀ j < J, j ∉ initial)
    (hgaps : ∀ j < J, 2 ∣ gap j ∧
      bridgeGapLower X (bridgeIteration X R₀ j) < (gap j : ℝ) ∧
      (gap j : ℝ) ≤ bridgeIteration X R₀ j) :
    ∀ j ≤ J,
      CompleteEvenGrid (initial ∪ Finset.range j) gap
          (radius + ∑ i ∈ Finset.range j, gap i) ∧
        2 ∣ radius + ∑ i ∈ Finset.range j, gap i ∧
        bridgeIteration X R₀ j ≤ ((radius + ∑ i ∈ Finset.range j, gap i : ℕ) : ℝ) := by
  intro j hj
  induction j with
  | zero => simpa [bridgeIteration] using And.intro hgrid (And.intro hradius hcoverage)
  | succ j ih =>
    have hjJ : j < J := by omega
    have ⟨hprevGrid, hprevEven, hprevCoverage⟩ := ih (by omega)
    have ⟨hgapEven, hgapLower, hgapUpper⟩ := hgaps j hjJ
    have hnew : j ∉ initial ∪ Finset.range j := by
      simp [hfresh j hjJ]
    have hstep := bridge_extends_grid_from_lower_bound
      (initial ∪ Finset.range j) gap (radius + ∑ i ∈ Finset.range j, gap i) j
      X (bridgeIteration X R₀ j) hnew hprevEven hgapEven hprevCoverage hgapLower
      hgapUpper hprevGrid
    have hset : initial ∪ Finset.range (j + 1) = insert j (initial ∪ Finset.range j) := by
      rw [Finset.range_add_one, Finset.union_insert]
    have hsum : (radius + ∑ i ∈ Finset.range (j + 1), gap i) =
        (radius + ∑ i ∈ Finset.range j, gap i) + gap j := by
      rw [Finset.sum_range_succ]
      omega
    refine ⟨?_, ?_, ?_⟩
    · rw [hset, hsum]
      exact hstep.1
    · rw [hsum]
      exact dvd_add hprevEven hgapEven
    · rw [hsum]
      change bridgeNext X (bridgeIteration X R₀ j) ≤ _
      rw [bridgeNext, if_pos (hbelow j hjJ)]
      exact le_of_lt hstep.2

/-- If every preterminal stage can supply a fresh admissible gap, the
finite source recurrence completes an actual even grid through X. The
stage-by-stage supply is a hypothesis, not an imported controller result. -/
theorem bridgeIteration_completes_grid (X R₀ : ℝ) (initial : Finset ℕ)
    (gap : ℕ → ℕ) (radius : ℕ) (hX : 0 < X) (hR : 0 < R₀)
    (hgrid : CompleteEvenGrid initial gap radius) (hradius : 2 ∣ radius)
    (hcoverage : R₀ ≤ (radius : ℝ))
    (hfresh : ∀ j, bridgeIteration X R₀ j < X → j ∉ initial)
    (hgaps : ∀ j, bridgeIteration X R₀ j < X → 2 ∣ gap j ∧
      bridgeGapLower X (bridgeIteration X R₀ j) < (gap j : ℝ) ∧
      (gap j : ℝ) ≤ bridgeIteration X R₀ j) :
    ∃ J : ℕ, (∀ j < J, bridgeIteration X R₀ j < X) ∧
      CompleteEvenGrid (initial ∪ Finset.range J) gap
        (radius + ∑ i ∈ Finset.range J, gap i) ∧
      X ≤ ((radius + ∑ i ∈ Finset.range J, gap i : ℕ) : ℝ) := by
  obtain ⟨J, hstop, hbelow⟩ := bridgeIteration_terminates X R₀ hX hR
  have hseq := bridgeIteration_preserves_grids X R₀ initial gap radius J hgrid hradius
    hcoverage hbelow (fun j hj => hfresh j (hbelow j hj))
    (fun j hj => hgaps j (hbelow j hj)) J le_rfl
  exact ⟨J, hbelow, hseq.1, le_trans hstop hseq.2.2⟩

end
end Sude
