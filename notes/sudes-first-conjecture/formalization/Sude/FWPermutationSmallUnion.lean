import Sude.FWSmallCutGate
import Sude.FWPermutationLargeUnion

/-! FW's small-cut union bound, retaining the strict source split and the
conditioning budget. No global expansion graph is asserted here. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- Common geometric base for the finite controller's small cuts. -/
noncomputable def fwSmallCutBase : ℝ :=
  Real.exp (1 + 3 * Real.binEntropy ((173 : ℝ) / 1000) +
    (1481 / 1000 : ℝ) * Real.log (1 / 256))

theorem fw_smallCutBase_lt : fwSmallCutBase < 1 / 216 := by
  have hg := fw_small_cut_gate
  have he := (Real.exp_lt_exp).2 hg
  have he3 : Real.exp (3 * Real.log 3) = 27 := by
    rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  have he8 : Real.exp (Real.log (1 / 8)) = (1 : ℝ) / 8 := Real.exp_log (by norm_num)
  have hid : 1 + 3 * Real.binEntropy ((173 : ℝ) / 1000) +
      (1481 / 1000 : ℝ) * Real.log (1 / 256) + 3 * Real.log 3 =
      (1 + 3 * Real.binEntropy ((173 : ℝ) / 1000) +
        (1481 / 1000 : ℝ) * Real.log (1 / 256)) + 3 * Real.log 3 := by ring
  rw [hid, Real.exp_add, he3, he8] at he
  dsimp [fwSmallCutBase]
  linarith

/-- One small-cut size contributes at most the corresponding power of the
source's geometric base, after the exact subset multiplicity is included. -/
theorem fw_small_cut_summand_bound {n s : ℕ} (hs : 0 < s) (hsmall : 256 * s < n) :
    ((Nat.choose n s : ℝ) * (fwPermutationFixedCutCount n s : ℝ)) / (n.factorial : ℝ)^3 ≤
      fwSmallCutBase ^ s := by
  let S := permutationCanonicalCut n s
  let t : ℝ := (s : ℝ) / n
  let q : ℕ := 519 * s / 1000
  let K : ℕ := 3 * s - q
  let C : ℝ := 1 + 3 * Real.binEntropy ((173 : ℝ) / 1000) +
    (1481 / 1000 : ℝ) * Real.log (1 / 256)
  have hslt : s < n := by omega
  have hcard : S.card = s := permutationCanonicalCut_card (by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have ht0 : 0 < t := div_pos hsR hnR
  have hsmallR : (256 : ℝ) * s ≤ n := by exact_mod_cast (show 256 * s ≤ n by omega)
  have htbound : t ≤ 1 / 256 := by
    dsimp [t]
    apply (div_le_iff₀ hnR).2
    linarith
  have hlog : Real.log t ≤ Real.log (1 / 256) := Real.log_le_log ht0 htbound
  have hlog0 : Real.log t ≤ 0 := le_trans hlog (Real.log_nonpos (by norm_num) (by norm_num))
  have hq : 1000 * q ≤ 519 * s := by dsimp [q]; omega
  have hqR : (1000 : ℝ) * q ≤ 519 * s := by exact_mod_cast hq
  have hq2 : q ≤ 2 * s := by dsimp [q]; omega
  have hK : ((K : ℕ) : ℝ) - s ≥ (1481 / 1000 : ℝ) * s := by
    dsimp [K]
    rw [Nat.cast_sub (by omega : q ≤ 3 * s)]
    push_cast
    linarith
  have hprod1 := mul_le_mul_of_nonpos_right hK hlog0
  have hprod2 := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (1481 / 1000 : ℝ) * s by positivity)
  have hexponent : (s : ℝ) * (1 - Real.log t) +
      (3 * (s : ℝ)) * Real.binEntropy ((173 : ℝ) / 1000) + (K : ℝ) * Real.log t ≤
        (s : ℝ) * C := by
    dsimp [C]
    nlinarith
  have hchoose := choose_le_exp_one_sub_log hs hslt
  have hfixed := fwPermutationFixedCutBad_exception_entropy_bound S (show 0 < n by omega) (by simpa [hcard] using hs)
  have hfixed' : (fwPermutationFixedCutCount n s : ℝ) / (n.factorial : ℝ)^3 ≤
      Real.exp ((3 * (s : ℝ)) * Real.binEntropy ((173 : ℝ) / 1000)) * t^K := by
    simpa [fwPermutationFixedCutCount, S, t, K, q, hcard, Nat.cast_mul] using hfixed
  have hmul := mul_le_mul hchoose hfixed' (by positivity) (Real.exp_nonneg _)
  have hexp : Real.exp ((s : ℝ) * (1 - Real.log t)) *
      (Real.exp ((3 * (s : ℝ)) * Real.binEntropy ((173 : ℝ) / 1000)) * t^K) =
        Real.exp ((s : ℝ) * (1 - Real.log t) +
          (3 * (s : ℝ)) * Real.binEntropy ((173 : ℝ) / 1000) + (K : ℝ) * Real.log t) := by
    have hKexp : Real.exp ((K : ℝ) * Real.log t) = t^K := by
      rw [Real.exp_nat_mul, Real.exp_log ht0]
    rw [Real.exp_add, Real.exp_add, hKexp]
    ring
  calc
    _ = (n.choose s : ℝ) * ((fwPermutationFixedCutCount n s : ℝ) / (n.factorial : ℝ)^3) := by ring
    _ ≤ _ := hmul
    _ = _ := hexp
    _ ≤ Real.exp ((s : ℝ) * C) := (Real.exp_le_exp).2 hexponent
    _ = fwSmallCutBase ^ s := by
      rw [Real.exp_nat_mul]
      rfl

/-- The empty cut can never fail expansion. -/
theorem fwPermutationFixedCutCount_zero (n : ℕ) : fwPermutationFixedCutCount n 0 = 0 := by
  classical
  have hcanon : permutationCanonicalCut n 0 = ∅ := by
    ext x
    simp [permutationCanonicalCut]
  have hbad : fwPermutationFixedCutBad (∅ : Finset (Fin n)) = ∅ := by
    ext p
    simp [fwPermutationFixedCutBad, fwPermutationCutFailure, cutEdges]
  simp [fwPermutationFixedCutCount, hcanon, hbad]

/-- The small-cut union is bounded by a geometric series, with the empty
cut removed explicitly. -/
theorem fw_small_cut_sum_bound {n : ℕ} (_hn : 0 < n) :
    ((∑ s ∈ permutationSmallSizes n, Nat.choose n s * fwPermutationFixedCutCount n s : ℕ) : ℝ) /
      (n.factorial : ℝ)^3 ≤ 1 / 215 := by
  classical
  let A := (permutationSmallSizes n).filter (fun s => 0 < s)
  let term : ℕ → ℝ := fun s => ((Nat.choose n s : ℝ) * (fwPermutationFixedCutCount n s : ℝ)) /
    (n.factorial : ℝ)^3
  have hzero : ∀ s ∈ permutationSmallSizes n, s ∉ A → term s = 0 := by
    intro s hs hnot
    have hs0 : s = 0 := by
      have hnot' : ¬ 0 < s := by
        intro hp
        apply hnot
        exact Finset.mem_filter.mpr ⟨hs, hp⟩
      omega
    subst s
    simp [term, fwPermutationFixedCutCount_zero]
  have hrestrict : (∑ s ∈ permutationSmallSizes n, term s) = ∑ s ∈ A, term s := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro s hs hnot
    exact hzero s hs hnot
  have hbase0 : 0 ≤ fwSmallCutBase := by unfold fwSmallCutBase; positivity
  have hbase : fwSmallCutBase ≤ (1 : ℝ) / 216 := fw_smallCutBase_lt.le
  have hpoint : ∀ s ∈ A, term s ≤ ((1 : ℝ) / 216)^s := by
    intro s hs
    have hs' := Finset.mem_filter.mp hs
    have hrange := (Finset.mem_filter.mp hs'.1).2
    exact (fw_small_cut_summand_bound hs'.2 hrange.2).trans (pow_le_pow_left₀ hbase0 hbase s)
  have hsubset : A ⊆ Finset.Ico 1 (n + 1) := by
    intro s hs
    have hs' := Finset.mem_filter.mp hs
    have hrange := (Finset.mem_filter.mp hs'.1).1
    have hslt : s < n + 1 := Finset.mem_range.mp hrange
    exact Finset.mem_Ico.mpr ⟨by omega, hslt⟩
  have hsum : (∑ s ∈ A, term s) ≤ ∑ s ∈ Finset.Ico 1 (n + 1), ((1 : ℝ) / 216)^s := by
    calc
      _ ≤ ∑ s ∈ A, ((1 : ℝ) / 216)^s := Finset.sum_le_sum hpoint
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset (by intro i hi hi'; positivity)
  have hgeom : (∑ s ∈ Finset.Ico 1 (n + 1), ((1 : ℝ) / 216)^s) ≤ 1 / 215 := by
    have h := geom_sum_Ico_le_of_lt_one (x := (1 : ℝ) / 216) (m := 1) (n := n + 1)
      (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hcast : ((∑ s ∈ permutationSmallSizes n, Nat.choose n s * fwPermutationFixedCutCount n s : ℕ) : ℝ) /
      (n.factorial : ℝ)^3 = ∑ s ∈ permutationSmallSizes n, term s := by
    dsimp [term]
    push_cast
    rw [Finset.sum_div]
  rw [hcast, hrestrict]
  exact hsum.trans hgeom

/-- The small-cut sum is strictly below the numerical `1/189` budget for
every positive order. The one-in-27 derangement bound applies when `n ≥ 2`. -/
theorem fw_small_cut_integer_budget {n : ℕ} (hn : 0 < n) :
    189 * (∑ s ∈ permutationSmallSizes n, Nat.choose n s * fwPermutationFixedCutCount n s) <
      (n.factorial)^3 := by
  have h := fw_small_cut_sum_bound hn
  have hF : 0 < (n.factorial : ℝ)^3 := pow_pos (by exact_mod_cast Nat.factorial_pos n) _
  have hreal : (189 : ℝ) *
      ((∑ s ∈ permutationSmallSizes n, Nat.choose n s * fwPermutationFixedCutCount n s : ℕ) : ℝ) <
      (n.factorial : ℝ)^3 := by
    have h' := (div_le_iff₀ hF).1 h
    nlinarith
  exact_mod_cast hreal

/-- Union over the smaller-side representatives of strict FW small cuts. -/
def fwPermutationSmallCutBad (n : ℕ) : Finset (Fin 3 → Equiv.Perm (Fin n)) :=
  (permutationSmallCuts n).biUnion fwPermutationFixedCutBad

/-- A failed cut in the strict small regime is represented in the event,
including when the named side is the larger side. -/
theorem fw_small_cut_mem_of_failure {n : ℕ} {p : Fin 3 → Equiv.Perm (Fin n)}
    (S : Finset (Fin n)) (hsmall : 256 * min S.card (n - S.card) < n)
    (hfail : fwPermutationCutFailure p S) : p ∈ fwPermutationSmallCutBad n := by
  classical
  have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
  by_cases hhalf : 2 * S.card ≤ n
  · apply Finset.mem_biUnion.mpr
    refine ⟨S, ?_, ?_⟩
    · simp only [permutationSmallCuts, Finset.mem_filter, Finset.mem_univ, true_and]
      have hm : min S.card (n - S.card) = S.card := Nat.min_eq_left (by omega)
      rw [hm] at hsmall
      exact ⟨hhalf, hsmall⟩
    · simpa [fwPermutationFixedCutBad] using hfail
  · apply Finset.mem_biUnion.mpr
    refine ⟨Sᶜ, ?_, ?_⟩
    · simp only [permutationSmallCuts, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.card_compl, Fintype.card_fin]
      have hm : min S.card (n - S.card) = n - S.card := Nat.min_eq_right (by omega)
      rw [hm] at hsmall
      exact ⟨by omega, hsmall⟩
    · simpa [fwPermutationFixedCutBad] using
        (fwPermutationCutFailure_compl p S).mpr hfail

/-- The small-cut union is bounded by the exact sum grouped by cut size. -/
theorem fw_small_cut_union_card (n : ℕ) :
    (fwPermutationSmallCutBad n).card ≤
      ∑ s ∈ permutationSmallSizes n, Nat.choose n s * fwPermutationFixedCutCount n s := by
  classical
  have h := Finset.card_biUnion_le (s := permutationSmallCuts n) (t := fwPermutationFixedCutBad)
  change (fwPermutationSmallCutBad n).card ≤ _ at h
  have hcuts : permutationSmallCuts n =
      permutationCutsOfSize n (fun s => 2 * s ≤ n ∧ 256 * s < n) := rfl
  rw [hcuts, fw_sum_cuts_by_size] at h
  exact h

/-- The unconditional small-cut failure probability is at most `1/215`;
this does not condition on derangements or estimate the large cuts. -/
theorem fw_small_cut_union_probability {n : ℕ} (hn : 0 < n) :
    ((fwPermutationSmallCutBad n).card : ℝ) / (n.factorial : ℝ)^3 ≤ 1 / 215 := by
  have h := fw_small_cut_union_card n
  have hr : ((fwPermutationSmallCutBad n).card : ℝ) ≤
      ((∑ s ∈ permutationSmallSizes n, Nat.choose n s * fwPermutationFixedCutCount n s : ℕ) : ℝ) := by
    exact_mod_cast h
  exact (div_le_div_of_nonneg_right hr (by positivity)).trans (fw_small_cut_sum_bound hn)

/-- The small-cut event has the strict numerical `1/189` budget for every
positive order. The one-in-27 derangement bound applies when `n ≥ 2`. -/
theorem fw_small_cut_union_integer_budget {n : ℕ} (hn : 0 < n) :
    189 * (fwPermutationSmallCutBad n).card < (n.factorial)^3 := by
  have h := fw_small_cut_union_card n
  have hb := fw_small_cut_integer_budget hn
  omega

end
end Sude
