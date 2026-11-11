import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Tactic

/-! The exact-cardinality sliding-window step in central completion CC2. -/
namespace Sude
noncomputable section

/-- A finite path crossing a target with jumps at most `2 * η` contains a
point at distance at most `η`. No independence or monotonicity is needed. -/
theorem finite_path_near_crossing (w : ℕ → ℝ) (m : ℕ) (target η : ℝ)
    (hη : 0 ≤ η) (hleft : w 0 ≤ target) (hright : target ≤ w m)
    (hjump : ∀ k < m, w (k + 1) - w k ≤ 2 * η) :
    ∃ k ≤ m, |w k - target| ≤ η := by
  classical
  by_cases hzero : target ≤ w 0
  · refine ⟨0, Nat.zero_le _, ?_⟩
    have : w 0 = target := le_antisymm hleft hzero
    simp [this, hη]
  · have hex : ∃ k : ℕ, k ≤ m ∧ target ≤ w k := ⟨m, le_rfl, hright⟩
    let k := Nat.find hex
    have hk : k ≤ m ∧ target ≤ w k := Nat.find_spec hex
    have hkpos : 0 < k := by
      by_contra h
      have : k = 0 := by omega
      exact hzero (this ▸ hk.2)
    have hprevlt : k - 1 < k := by omega
    have hprev : w (k - 1) < target := by
      have hnot := Nat.find_min hex hprevlt
      have hp : k - 1 ≤ m := by omega
      have : ¬ target ≤ w (k - 1) := fun h => hnot ⟨hp, h⟩
      exact lt_of_not_ge this
    have hstep := hjump (k - 1) (by omega)
    have hsucc : k - 1 + 1 = k := by omega
    rw [hsucc] at hstep
    by_cases hclose : target - w (k - 1) ≤ η
    · refine ⟨k - 1, by omega, ?_⟩
      rw [abs_le]
      constructor <;> linarith
    · refine ⟨k, hk.1, ?_⟩
      rw [abs_le]
      constructor <;> linarith

def centralWindow (v : ℕ → ℝ) (q k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico k (k + q), v i

/-- Adjacent fixed-size windows exchange exactly one value. -/
theorem centralWindow_step (v : ℕ → ℝ) (q k : ℕ) :
    centralWindow v q (k + 1) - centralWindow v q k = v (k + q) - v k := by
  unfold centralWindow
  rw [Finset.sum_Ico_eq_sub _ (by omega), Finset.sum_Ico_eq_sub _ (by omega)]
  have h : k + 1 + q = k + q + 1 := by omega
  rw [h, Finset.sum_range_succ, Finset.sum_range_succ]
  ring

/-- If the first and last ordered windows bracket the current mean, a
window gives a distinct exact-cardinality subset with CC2's `η` error.
This includes `q = 0`. Bracketing from the two outer stocks is a separate
obligation and is not assumed to follow from the central count alone. -/
theorem central_window_select (v : ℕ → ℝ) (M q : ℕ) (c η ν : ℝ)
    (hη : 0 ≤ η) (hq : q ≤ M)
    (hinj : ∀ i < M, ∀ j < M, v i = v j → i = j)
    (hinterval : ∀ i < M, |v i - c| ≤ η)
    (hleft : centralWindow v q 0 ≤ (q : ℝ) * ν)
    (hright : (q : ℝ) * ν ≤ centralWindow v q (M - q)) :
    ∃ T : Finset ℝ, T ⊆ (Finset.range M).image v ∧ T.card = q ∧
      |(∑ x ∈ T, x) - (q : ℝ) * ν| ≤ η := by
  classical
  have hjump : ∀ k < M - q,
      centralWindow v q (k + 1) - centralWindow v q k ≤ 2 * η := by
    intro k hk
    rw [centralWindow_step]
    have h₁ := abs_le.mp (hinterval k (by omega))
    have h₂ := abs_le.mp (hinterval (k + q) (by omega))
    linarith
  obtain ⟨k, hk, hnear⟩ := finite_path_near_crossing (centralWindow v q) (M - q)
    ((q : ℝ) * ν) η hη hleft hright hjump
  let I := Finset.Ico k (k + q)
  have hI : I ⊆ Finset.range M := by
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    exact Finset.mem_range.mpr (by omega)
  have hv : Set.InjOn v (↑I : Set ℕ) := by
    intro i hi j hj h
    exact hinj i (Finset.mem_range.mp (hI hi)) j (Finset.mem_range.mp (hI hj)) h
  refine ⟨I.image v, Finset.image_subset_image hI, ?_, ?_⟩
  · rw [Finset.card_image_iff.mpr hv]
    simp [I]
  · rw [Finset.sum_image hv]
    exact hnear

/-- Sorted values with at least `q` below and `q` above the current mean
bracket that mean by the first and last `q`-element windows. -/
theorem central_window_bracket_of_counts (v : ℕ → ℝ) (M q : ℕ) (ν : ℝ)
    (hq : q ≤ M)
    (hsorted : ∀ i j, i ≤ j → j < M → v i ≤ v j)
    (hlow : q ≤ ((Finset.range M).filter (fun i => v i ≤ ν)).card)
    (hhigh : q ≤ ((Finset.range M).filter (fun i => ν ≤ v i)).card) :
    centralWindow v q 0 ≤ (q : ℝ) * ν ∧
      (q : ℝ) * ν ≤ centralWindow v q (M - q) := by
  classical
  have hfirst : ∀ i < q, v i ≤ ν := by
    intro i hi
    by_contra h
    have hgt : ν < v i := lt_of_not_ge h
    have hsub : (Finset.range M).filter (fun j => v j ≤ ν) ⊆ Finset.range i := by
      intro j hj
      obtain ⟨hjM, hjv⟩ := Finset.mem_filter.mp hj
      have hjM' := Finset.mem_range.mp hjM
      apply Finset.mem_range.mpr
      by_contra hji
      have hij : i ≤ j := by omega
      have hle := hsorted i j hij hjM'
      linarith
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_range] at hc
    omega
  have hlast : ∀ i, M - q ≤ i → i < M → ν ≤ v i := by
    intro i hi hiM
    by_contra h
    have hlt : v i < ν := lt_of_not_ge h
    have hsub : (Finset.range M).filter (fun j => ν ≤ v j) ⊆ Finset.Ico (i + 1) M := by
      intro j hj
      obtain ⟨hjM, hjv⟩ := Finset.mem_filter.mp hj
      have hjM' := Finset.mem_range.mp hjM
      apply Finset.mem_Ico.mpr
      refine ⟨?_, hjM'⟩
      by_contra hji
      have hji' : j ≤ i := by omega
      have hle := hsorted j i hji' hiM
      linarith
    have hc := Finset.card_le_card hsub
    simp only [Nat.card_Ico] at hc
    omega
  constructor
  · unfold centralWindow
    calc
      ∑ i ∈ Finset.Ico 0 (0 + q), v i ≤ ∑ _i ∈ Finset.Ico 0 (0 + q), ν := by
        apply Finset.sum_le_sum
        intro i hi
        apply hfirst
        have := (Finset.mem_Ico.mp hi).2
        omega
      _ = (q : ℝ) * ν := by simp
  · unfold centralWindow
    calc
      (q : ℝ) * ν = ∑ _i ∈ Finset.Ico (M - q) (M - q + q), ν := by
        have hc : (Finset.Ico (M - q) (M - q + q)).card = q := by
          simp only [Nat.card_Ico]
          omega
        rw [Finset.sum_const, hc]
        simp
      _ ≤ ∑ i ∈ Finset.Ico (M - q) (M - q + q), v i := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_Ico.mp hi
        apply hlast i hi'.1
        omega

/-- CC2 selection from explicit two-sided stocks, including empty batches.
The `M` listed values are distinct; no replacement sampling is used. -/
theorem central_window_select_from_counts (v : ℕ → ℝ) (M q : ℕ) (c η ν : ℝ)
    (hη : 0 ≤ η) (hq : q ≤ M)
    (hinj : ∀ i < M, ∀ j < M, v i = v j → i = j)
    (hsorted : ∀ i j, i ≤ j → j < M → v i ≤ v j)
    (hinterval : ∀ i < M, |v i - c| ≤ η)
    (hlow : q ≤ ((Finset.range M).filter (fun i => v i ≤ ν)).card)
    (hhigh : q ≤ ((Finset.range M).filter (fun i => ν ≤ v i)).card) :
    ∃ T : Finset ℝ, T ⊆ (Finset.range M).image v ∧ T.card = q ∧
      |(∑ x ∈ T, x) - (q : ℝ) * ν| ≤ η := by
  obtain ⟨hl, hr⟩ := central_window_bracket_of_counts v M q ν hq hsorted hlow hhigh
  exact central_window_select v M q c η ν hη hq hinj hinterval hl hr

end
end Sude
