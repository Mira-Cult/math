import Sude.PhysicalCutRouting
import Sude.FTTTargetList

/-! Actual accumulated even-gap grids, midpoint rounding, and prime-target
interfaces. Prime supplies and controller estimates are not assumed proved. -/
namespace Sude
noncomputable section

/-- Each new gap joins the complete grid available immediately before it;
`R` is the actual accumulated gap total, not a conservative lower bound. -/
inductive EvenGapChain {K : Type*} (gap : K → ℕ) : ℕ → List K → Prop
  | nil (R : ℕ) : EvenGapChain gap R []
  | cons (R : ℕ) (k : K) (ks : List K) :
      2 ∣ gap k → gap k ≤ R + 2 → EvenGapChain gap (R + gap k) ks →
      EvenGapChain gap R (k :: ks)

/-- Appending distinct joined gaps preserves all even subset sums through the
actual total. This works for arbitrary supplied gaps and all stage counts. -/
theorem extend_even_gap_chain {K : Type*} [DecidableEq K]
    (gap : K → ℕ) (base : Finset K) (R : ℕ) (ks : List K)
    (hbase : CompleteEvenGrid base gap R) (heven : 2 ∣ R)
    (hnodup : ks.Nodup) (hfresh : ∀ k ∈ ks, k ∉ base)
    (hchain : EvenGapChain gap R ks) :
    CompleteEvenGrid (base ∪ ks.toFinset) gap (R + (ks.map gap).sum) := by
  induction hchain generalizing base with
  | nil R => simpa using hbase
  | cons R k ks hkEven hjoin htail ih =>
    have hn : k ∉ ks := (List.nodup_cons.mp hnodup).1
    have hnd : ks.Nodup := (List.nodup_cons.mp hnodup).2
    have hk : k ∉ base := hfresh k (by simp)
    have hf : ∀ j ∈ ks, j ∉ insert k base := by
      intro j hj
      simp only [Finset.mem_insert, not_or]
      refine ⟨?_, hfresh j (by simp [hj])⟩
      intro h
      subst j
      exact hn hj
    have hnew := completeEvenGrid_insert base gap R k hk heven hkEven hjoin hbase
    have hevenNew : 2 ∣ R + gap k := dvd_add heven hkEven
    have hresult := ih (insert k base) hnew hevenNew hnd hf
    simpa [List.toFinset_cons, Finset.union_insert, Finset.insert_union, add_assoc,
      add_comm, add_left_comm] using hresult

/-- When the base radius is its full gap total, the extended grid radius
is exactly the total gap in all physical labels. -/
theorem extend_even_gap_chain_actual_total {K : Type*} [DecidableEq K]
    (gap : K → ℕ) (base : Finset K) (ks : List K)
    (hbase : CompleteEvenGrid base gap (∑ k ∈ base, gap k))
    (heven : 2 ∣ ∑ k ∈ base, gap k)
    (hnodup : ks.Nodup) (hfresh : ∀ k ∈ ks, k ∉ base)
    (hchain : EvenGapChain gap (∑ k ∈ base, gap k) ks) :
    CompleteEvenGrid (base ∪ ks.toFinset) gap
      (∑ k ∈ base ∪ ks.toFinset, gap k) := by
  have hgrid := extend_even_gap_chain gap base _ ks hbase heven hnodup hfresh hchain
  have hdisj : Disjoint base ks.toFinset := by
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    exact hfresh k (List.mem_toFinset.mp hk') hk
  have hsum : (∑ k ∈ base ∪ ks.toFinset, gap k) =
      (∑ k ∈ base, gap k) + (ks.map gap).sum := by
    rw [Finset.sum_union hdisj]
    rw [List.sum_toFinset gap hnodup]
  simpa only [hsum] using hgrid

/-- The finite binary prefix supplies a full grid through its own actual
gap total, provided its labelled gaps are the stated powers of two. -/
theorem binary_prefix_actual_grid (P : ℕ) (gap : ℕ → ℕ)
    (hgap : ∀ k < P, gap k = 2 ^ (k + 1)) :
    CompleteEvenGrid (Finset.range P) gap (∑ k ∈ Finset.range P, gap k) ∧
      2 ∣ ∑ k ∈ Finset.range P, gap k := by
  have hsum : (∑ k ∈ Finset.range P, gap k) = 2 ^ (P + 1) - 2 := by
    calc
      _ = ∑ k ∈ Finset.range P, 2 ^ (k + 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hgap k (Finset.mem_range.mp hk)
      _ = _ := binary_gap_total P
  constructor
  · intro t ht heven
    obtain ⟨T, hT, hTsum⟩ := binary_even_grid P t heven (hsum ▸ ht)
    refine ⟨T, hT, ?_⟩
    calc
      _ = ∑ k ∈ T, 2 ^ (k + 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hgap k (Finset.mem_range.mp (hT hk))
      _ = t := hTsum
  · apply Finset.dvd_sum
    intro k hk
    rw [hgap k (Finset.mem_range.mp hk), pow_succ]
    exact dvd_mul_left 2 (2 ^ k)


/-- The doubled deviation from the sum of true pair midpoints is exactly
the total physical gap minus twice the gap of the selected reversed pairs. -/
theorem oriented_pairs_midpoint_identity {K : Type*} [DecidableEq K]
    (S T : Finset K) (low high gap : K → ℕ) (hT : T ⊆ S)
    (hgap : ∀ k ∈ S, high k = low k + gap k) :
    2 * (∑ k ∈ S, (if k ∈ T then (low k : ℤ) else (high k : ℤ))) -
      (∑ k ∈ S, ((low k : ℤ) + (high k : ℤ))) =
      (∑ k ∈ S, (gap k : ℤ)) - 2 * (∑ k ∈ T, (gap k : ℤ)) := by
  classical
  have hsel : (∑ k ∈ S, if k ∈ T then (gap k : ℤ) else 0) =
      ∑ k ∈ T, (gap k : ℤ) := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hT]
  calc
    _ = ∑ k ∈ S, (2 * (if k ∈ T then (low k : ℤ) else (high k : ℤ)) -
          ((low k : ℤ) + high k)) := by
      simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = ∑ k ∈ S, ((gap k : ℤ) - 2 * (if k ∈ T then (gap k : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hg : (high k : ℤ) = (low k : ℤ) + gap k := by exact_mod_cast hgap k hk
      by_cases ht : k ∈ T <;> simp [ht] <;> omega
    _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsel]

/-- An orientation centered at the actual even gap total is within one unit
of the true aggregate midpoint. The displayed integer bound is doubled, so
no rounding or division is hidden. -/
theorem oriented_pairs_midpoint_error {K : Type*} [DecidableEq K]
    (S T : Finset K) (low high gap : K → ℕ) (hT : T ⊆ S)
    (hgap : ∀ k ∈ S, high k = low k + gap k)
    (heven : ∀ k ∈ S, 2 ∣ gap k)
    (hcenter : (∑ k ∈ T, gap k) = evenGridCenter (∑ k ∈ S, gap k)) :
    0 ≤ 2 * (∑ k ∈ S, (if k ∈ T then (low k : ℤ) else (high k : ℤ))) -
      (∑ k ∈ S, ((low k : ℤ) + (high k : ℤ))) ∧
    2 * (∑ k ∈ S, (if k ∈ T then (low k : ℤ) else (high k : ℤ))) -
      (∑ k ∈ S, ((low k : ℤ) + (high k : ℤ))) ≤ 2 := by
  have hR : 2 ∣ ∑ k ∈ S, gap k := Finset.dvd_sum heven
  have ⟨hlo, hhi⟩ := evenGridCenter_midpoint_error (∑ k ∈ S, gap k) hR
  have hloZ : (2 : ℤ) * evenGridCenter (∑ k ∈ S, gap k) ≤ (∑ k ∈ S, gap k : ℕ) := by
    exact_mod_cast hlo
  have hnat : (∑ k ∈ S, gap k) ≤ 2 * evenGridCenter (∑ k ∈ S, gap k) + 2 := by omega
  have hnatZ : ((∑ k ∈ S, gap k : ℕ) : ℤ) ≤
      2 * (evenGridCenter (∑ k ∈ S, gap k) : ℤ) + 2 := by exact_mod_cast hnat
  rw [oriented_pairs_midpoint_identity S T low high gap hT hgap]
  have hcZ : (∑ k ∈ T, (gap k : ℤ)) = evenGridCenter (∑ k ∈ S, gap k) := by exact_mod_cast hcenter
  have htotal : (∑ k ∈ S, (gap k : ℤ)) = ((∑ k ∈ S, gap k : ℕ) : ℤ) := by simp
  rw [hcZ, htotal]
  constructor <;> omega

/-- A complete grid through its actual total contains a physical reference
orientation with the proved aggregate midpoint error. -/
theorem complete_grid_has_true_midpoint_reference {K : Type*} [DecidableEq K]
    (S : Finset K) (low high gap : K → ℕ)
    (hgap : ∀ k ∈ S, high k = low k + gap k)
    (heven : ∀ k ∈ S, 2 ∣ gap k)
    (hgrid : CompleteEvenGrid S gap (∑ k ∈ S, gap k)) :
    ∃ T ⊆ S,
      (∑ k ∈ T, gap k) = evenGridCenter (∑ k ∈ S, gap k) ∧
      0 ≤ 2 * (∑ k ∈ S, (if k ∈ T then (low k : ℤ) else (high k : ℤ))) -
        (∑ k ∈ S, ((low k : ℤ) + (high k : ℤ))) ∧
      2 * (∑ k ∈ S, (if k ∈ T then (low k : ℤ) else (high k : ℤ))) -
        (∑ k ∈ S, ((low k : ℤ) + (high k : ℤ))) ≤ 2 := by
  obtain ⟨T, hT, hsum⟩ := centered_even_grid S gap (∑ k ∈ S, gap k) hgrid 0
    (by norm_num) (by omega) (by omega)
  have hc : (∑ k ∈ T, gap k) = evenGridCenter (∑ k ∈ S, gap k) := by
    have hh : ((∑ k ∈ T, gap k : ℕ) : ℤ) = evenGridCenter (∑ k ∈ S, gap k) := by omega
    exact_mod_cast hh
  exact ⟨T, hT, hc, oriented_pairs_midpoint_error S T low high gap hT hgap heven hc⟩


end
end Sude
